class Floorplan { 
  public rooms: Array<Room> = []
  public doors: Array<Door> = []
  public paths: Array<Path> = []
  public cards: Array<Card> = []
  public verifier: Verifier = new Verifier(this, "ws://127.0.0.1:8080")
  public speed: number = 0.08  

  private emergency: boolean = false
  private reactor: Element

  private onCardAdded_ = new Publisher<Card>()
  public onCardAdded: IPublisher<Card> = this.onCardAdded_.expose()

  private onCardCountChange_ = new Publisher<number>()
  public onCardCountChange: IPublisher<number> = this.onCardCountChange_.expose()

  private cardSelection: Card | null = null
  public getSelectedCard() { return this.cardSelection }

  private onCardSelectionChange_ = new Publisher<Card | null>()
  public onCardSelectionChange = this.onCardSelectionChange_.expose()

  constructor(public svg: SVGElement) {
    svg.querySelectorAll('.room').forEach((elem: SVGElement) => {
      this.addRoom(new Room(elem,this))
    })
    let escapePlan = svg.querySelector("#escapePlan")
    svg.querySelectorAll('.door').forEach((elem: SVGGraphicsElement) => {
      let door = new Door(elem,this)    
      this.addDoor(door)
      if (!escapePlan) throw new Error("no escape plan")      
      escapePlan.appendChild(door.arrow)
    })
    svg.querySelectorAll('.path').forEach((elem: SVGPathElement) => {
      this.addPath(new Path(elem,true,this))
      this.addPath(new Path(elem,false,this))
    })
    this.reactor = (() => {
      let r = svg.querySelector('#reactor')
      if (!r) throw new Error("reactor is missing")   
      else return r})()
    this.reactor.addEventListener('click',() => this.toggleEmergency())
    this.verifier.onModeChange.listen(mode => {
      if (mode < VerificationMode.DoorAccess) {
        this.cards.forEach(card => card.leave())
      } else {
        this.cards.forEach(card => card.enter())
      }
    })
    let indicatorTimeout: number | null = null
    this.verifier.onStateChange.listen(verifing => {
      if (indicatorTimeout) {
        window.clearTimeout(indicatorTimeout)      
        indicatorTimeout = null
      }      
      if (verifing) {
        indicatorTimeout = window.setTimeout(() => 
          svg.querySelectorAll("#indicator").forEach(indicator => indicator.classList.add("visible"))
          , 500
        )
      } else 
        svg.querySelectorAll("#indicator").forEach(indicator => indicator.classList.remove("visible"))
    })
    this.rooms.forEach(room => {
      let entries = this.doors.filter(door => door.from == room || door.to == room)
      for (let a = 0; a < entries.length; a++) {
        for (let b = a + 1; b < entries.length; b++) {
          let p = this.paths.find(path => 
            path.room == room &&
            (path.from == entries[a] &&
            path.to == entries[b] ||
            path.from == entries[b] &&
            path.to == entries[a])
          )
          if (!p) console.warn(`No path for ${entries[a].id}-[${room.id}]-${entries[b].id}`)
        }
      }
    })
  }

  public getRoom(id: string): Room {
    let result = this.rooms.find(room => room.id == id)
    if (!result) throw new Error("room '" + id + "' does not exist")    
    return result!
  }

  public getDoor(id: string): Door | null {
    let result = this.doors.find(door => door.id == id)
    if (!result) throw new Error("door '" + id + "' does not exist")    
    return result!
  }

  public getPathsFrom(door: string): Path[] {
    return this.paths.filter(path => path.from && path.from.id == door)
  }

  public getPathsTo(door: string): Path[] {
    return this.paths.filter(path => path.to && path.to.id == door)
  }

  public addRoom(room: Room) {
    this.rooms.push(room)
    room.onClick.listen(() => {
      if (this.cardSelection) {    
        let card = this.cardSelection    
        this.verifier.verifyAccessRights(this.cardSelection,room).then(ok => {
          console.log(ok)          
          if (!ok.sat) {
            card.toggleAuthorization(room)
          } else {
            room.showError()
          }          
        })
      }
    })
  }

  public addDoor(door: Door) {    
    this.doors.push(door)
  }

  public addPath(path: Path) {
    this.paths.push(path)
  }

  private cancelEmergency: CancellationToken = CancellationToken.noop()
  public toggleEmergency(): boolean {
    this.emergency = !this.emergency
    if (this.emergency) {
      this.reactor.classList.add("emergency")
      this.verifier.getEscapePlan().then((res) => {
        console.log(res)
        this.doors.map(door => {          
          if (res.model.get(door.id + ".fromTo") == true)
            door.emergency(Direction.In)
          else if (res.model.get(door.id + ".toFrom") == true)
            door.emergency(Direction.Out)
          else door.emergency()
        })
      })
      this.svg.classList.add("emergency")      
    }
    else {      
      this.reactor.classList.remove("emergency")
      this.svg.classList.remove("emergency")
      this.cards.forEach(card => card.reenter())
      this.doors.forEach(door => door.reset())      
      this.doors.forEach(door => door.endEmergency())
    }
    return (this.emergency)
  }

  public isEmergency() {
    return this.emergency
  }
  
  public createCard() {
    let card = new Card(this)
    this.cards.push(card)
    if (this.cardSelection) {
      this.cardSelection.getAuthorizations().forEach(room => {
        card.addAuthorization(room)
      })
    }
    card.onSelected.listen(() => {
      this.cardSelection = card
      this.onCardSelectionChange_.publish(card)
      this.cards.forEach((card2) => {
        if (card2 != card) card2.deselect()
      })      
    })
    card.onDeselected.listen(() => {
      if (this.cardSelection == card) {
        this.cardSelection = null
        this.onCardSelectionChange_.publish(null)
      }
    })    
    /*card.onAuthorizationAdded.listen(() => {
      if (this.verifier.getMode() == VerificationMode.AccessRights) this.verifier.verify()
    })
    card.onAuthorizationRemoved.listen(() => {
      if (this.verifier.getMode() == VerificationMode.AccessRights) this.verifier.verify()
    })*/    
    let c = card.onRemove.listen(() => {
      this.cards.splice(this.cards.indexOf(card),1)      
      c.cancel()
      this.onCardCountChange_.publish(this.cards.length)
    })
    this.onCardAdded_.publish(card)
    this.onCardCountChange_.publish(this.cards.length)
  }

  public removeCard(card?: Card) {
    if (!card) {
      card = this.cards[this.cards.length - 1]      
    }
    card.remove()
  }
  
  public animate(dt: number) {
    if (this.emergency) {
      
    } else {
      this.cards.forEach(card => card.animate(dt * this.speed))
    }
  }
}