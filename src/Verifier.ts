enum VerificationMode {
  PreDeployment,
  Topology,
  AccessRights,
  DoorAccess,
  Emergency
}

class VerifierResult {
  public sat: boolean | null = null
  public model: Map<any,any> = new Map()
  constructor (sat?: boolean) {
    if (sat) this.sat = sat
  }
}

class Verifier {
  private mode: VerificationMode = VerificationMode.DoorAccess
  private socket: WebSocket
  private result = new VerifierResult()

  private onModeChange_ = new Publisher<VerificationMode>()
  public onModeChange = this.onModeChange_.expose()

  private onStateChange_ = new Publisher<boolean>()
  public onStateChange = this.onStateChange_.expose()

  private staticVariables: { name: string, type: string }[] = []
  private staticAssertions: string[] = []

  constructor(public floorplan: Floorplan, public url: string) {
  }

  public setMode(mode: VerificationMode) {        
    if (mode != this.mode) {
      this.mode = mode
      this.onModeChange_.publish(mode)    
    }
  }  

  public getMode(): VerificationMode {
    return this.mode
  }

  private resets: Array<(sat: VerifierResult) => void> = []
  private scheduled: Array<() => Array<string>> = []

  public schedule(lines: () => string[]): Promise<VerifierResult> { 
    if (this.resets.length > 0)
      this.scheduled.push(lines) 
    else {
      window.setTimeout(() => {
        this.onStateChange_.publish(true)      
        this.socket.send("(push)")
        lines().forEach(line => this.socket.send(line))
        this.socket.send('(pop)')
        this.socket.send(`(echo "reset")`)
      },0)
    }
    return new Promise((resolve,reject) => this.resets.push(resolve))     
  }

  private initStatic() {
    this.floorplan.doors.forEach(door => {
      this.staticVariables.push({
        name: `${door.id}.fromTo`,
        type: "Bool"
      },{
        name: `${door.id}.toFrom`,
        type: "Bool"
      })
      this.staticAssertions.push(
        `(not (and ${door.id}.fromTo ${door.id}.toFrom))`,
      )
    })
  }

  private safetyProperty(
    people: { index: number, authorisations: Set<Room> }[],    
  ): { variables: { name: string, type: string }[], assertions: string[] } {
    let variables: { name: string, type: string }[] = this.staticVariables.slice(0)
    let assertions: string[] = this.staticAssertions.slice(0)
    people.forEach((person,i) => {      
      this.floorplan.rooms.forEach(room => {
        variables.push({
          name: `${room.id}.card-${i}.hasAccess`,
          type: "Bool"
        })        
        if (!person.authorisations.has(room))
          assertions.push(
            `(not ${room.id}.card-${i}.hasAccess)`)
        let entries = this.floorplan.doors
          .filter(door => door.from == room || door.to == room)
          .map(door => {
            if (door.from == room) return `(and ${door.to.id}.card-${i}.hasAccess ${door.id}.toFrom)`
            else return `(and ${door.from.id}.card-${i}.hasAccess ${door.id}.fromTo)`
          })
        assertions.push(`(= ${room.id}.card-${i}.hasAccess (or (= card-${i} ${room.id}) ${entries.join(" ")}))`)              
      })      
      let exits = this.floorplan.rooms
        .filter(room => room.isEntry)
        .map(room => `${room.id}.card-${i}.hasAccess`)
      assertions.push(`(or ${exits.join(" ")})`)
    })
    // exists card positions -> not exists door combination
    return {
      variables: variables,
      assertions: assertions
    }
  }

  public verifyAccessRights(card_: Card, room_: Room): Promise<VerifierResult> {
    if (this.mode == VerificationMode.AccessRights) {
      return this.schedule(() => {
        let lines: string[] = []
        let z3 = (line: string) => {
          lines.push(line)
        }        
        this.floorplan.cards.forEach((card,i) => {      
          z3(`(declare-const card-${i} Int)`)
          let auths = new Set(card.getAuthorizations().values())
          if (card == card_) {
            if (auths.has(room_)) auths.delete(room_); else auths.add(room_)
          }
          let options = Array.from(auths).map(room => `(= card-${i} ${room.id})`)          
          z3(`(assert (or ${options.join(" ")}))`)
        })
        let prop = this.safetyProperty(this.floorplan.cards.map((card, i) => {
          let auths = new Set(card.getAuthorizations().values())
          if (card == card_) {
            if (auths.has(room_)) auths.delete(room_); else auths.add(room_)
          }
          return {
            index: i,
            authorisations: auths
          }
        }))
        let vars = prop.variables.map(variable => `(${variable.name} ${variable.type})`)
        console.log(vars)
        z3(`(assert (not (exists (${vars.join(' ')}) (and ${prop.assertions.join(' ')}))))`)
        z3("(check-sat)")
        this.floorplan.cards.forEach((card,i) => {
          z3(`(echo "card-${i}:")`)
          z3(`(eval card-${i} :completion true)`)
        })
        console.log(lines)
        return lines
        })
    } else {
      return Promise.resolve(new VerifierResult(false))
    }
  }

  public verifyDoorAccess(card_: Card, room_: Room): Promise<VerifierResult> {
    if (this.mode == VerificationMode.DoorAccess) {
      return this.schedule(() => {
        let lines: string[] = []
        let z3 = (line: string) => {
          lines.push(line)
        }
        this.floorplan.cards.forEach((card,i) => {
          let room = card == card_ ? room_ : card.getRoom()
          z3(`(define-fun card-${i} () Int ${room.id})`)
        })
        let prop = this.safetyProperty(this.floorplan.cards.map((card,i) => {
          return {
            index: i,
            authorisations: card.getAuthorizations()
          }
        }))
        prop.variables.forEach(variable => {
          z3(`(declare-const ${variable.name} ${variable.type})`)
        })
        prop.assertions.forEach(assertion => {
          z3(`(assert ${assertion})`)
        })
        z3("(check-sat)")
        return lines  
      })      
    } else {
      return Promise.resolve(new VerifierResult(true))
    }
  }
  
  public getEscapePlan(): Promise<VerifierResult> {
    return (this.schedule(() => {
      let lines: string[] = []
      let z3 = (line: string) => {
        lines.push(line)
      }
      this.floorplan.cards.forEach((card,i) => {      
        z3(`(define-fun card-${i} () Int ${card.getRoom().id})`)
      })
      let prop = this.safetyProperty(this.floorplan.cards.map((card,i) => {
        return {
          index: i,
          authorisations: card.getAuthorizations()
        }
      }))
      prop.variables.forEach(variable => {
        z3(`(declare-const ${variable.name} ${variable.type})`)
      })
      prop.assertions.forEach(assertion => {
        z3(`(assert ${assertion})`)
      })
      z3("(check-sat)")
      this.floorplan.doors.forEach(door => {
        z3(`(echo "${door.id}.fromTo:")`)
        z3(`(eval ${door.id}.fromTo :completion true)`)
        z3(`(echo "${door.id}.toFrom:")`)
        z3(`(eval ${door.id}.toFrom :completion true)`)
      })
      return lines
    }))
  }
  
}