class Card {  
  private path: Path | null  
  private position: number = 0  
  private moving: boolean = true    
  private forward: boolean = true
  public color: string
  private authorizations: Set<Room> = new Set()
  private timeout: number | null = 0  
  private action: () => void = () => { }
  private selected: boolean = false
  private elem: SVGCircleElement
  private floorplan: Floorplan  

  private onSelected_ = new Publisher<void>()
  public  onSelected  = this.onSelected_.expose()

  private onDeselected_ = new Publisher<void>()
  public  onDeselected  = this.onDeselected_.expose()
  
  private onReachedDoor_ = new Publisher<Door>()
  public onReachedDoor = this.onReachedDoor_.expose()

  private onRemove_ = new Publisher<void>()
  public onRemove = this.onRemove_.expose()

  private onAuthorizationAdded_ = new Publisher<Room>()
  public onAuthorizationAdded = this.onAuthorizationAdded_.expose()

  private onAuthorizationRemoved_ = new Publisher<Room>()
  public onAuthorizationRemoved = this.onAuthorizationRemoved_.expose()  

  constructor(floorplan: Floorplan) {
    this.floorplan = floorplan
    let h = Math.floor(Math.random() * 360)
    let s = (66 + Math.floor(Math.random() * 20))
    let l = (66 + Math.floor(Math.random() * 20))
    this.color = `hsl(${h},${s}%,${l}%)`    
    this.elem = document.createElementNS('http://www.w3.org/2000/svg','circle')
    this.elem.classList.add('person')
    let people = this.floorplan.svg.querySelector('#people')
    if (!people) throw new Error("cannot find #people")
    people.appendChild(this.elem)
    this.elem.r.baseVal.value = 4
    this.elem.style.fill = this.color   
    this.path = this.choosePath()
    this.floorplan.rooms.forEach(r => { if (r.isEntry) this.authorizations.add(r) })
  }

  public remove() {
    this.deselect()
    this.onRemove_.publish()
    let parent = this.elem.parentNode    
    if (parent) parent.removeChild(this.elem)
  }

  public hasAuthorization(room: Room): boolean {
    return room.isEntry || this.authorizations.has(room)
  }

  public getRoom(): Room {
    if (this.path) return this.path.room
    else {
      let res = this.floorplan.rooms.find(r => r.isEntry)
      if (!res) throw new Error("could not find an entry")
      return res
    }
  }

  public getAuthorizations(): Set<Room> {
    return this.authorizations
  }

  public addAuthorization = (room: Room) => { 
    let wasThere = this.hasAuthorization(room)
    this.authorizations.add(room)
    if (!wasThere) this.onAuthorizationAdded_.publish(room)
    if (!this.path) this.path = this.choosePath()
  }

  public removeAuthorization(room: Room) {    
    if (!room.isEntry) {
      if (this.authorizations.delete(room))      
        this.onAuthorizationRemoved_.publish(room)      
    }
  }

  public toggleAuthorization(room: Room): boolean {
    if (this.hasAuthorization(room)) {
      this.removeAuthorization(room)  
      return false
    } else {
      this.addAuthorization(room)
      return true
    }
  }

  public getPoint(): DOMPoint {
    return this.path ? this.path.at(this.position) : new DOMPoint(0,0)
  }  

  public select() {
    if (!this.selected) {
      this.elem.classList.add("active")
      this.selected = true
      this.onSelected_.publish()
    }
  }

  public deselect() {
    if (this.selected) {
      this.elem.classList.remove("active")
      this.selected = false
      this.onDeselected_.publish()
    }
  }

  public isSelected() { return this.selected }

  public choosePath = () => {
    let door = this.path ? (this.forward ? this.path.to : this.path.from) : null
    let room = this.path ? this.path.room : null
    if (door && room) {
      let otherSide = door.other(room)
      let options = this.floorplan.paths.filter(path =>
        path.from == door &&
        path.room == otherSide &&
        path.to != path.from && 
        this.hasAuthorization(path.room) &&
        (!path.to || this.hasAuthorization(path.to.other(otherSide))))
      if (options.length == 0) {
        options = this.floorplan.paths.filter(path =>
          path.from == door &&
          path.room == otherSide &&
          this.hasAuthorization(path.room) &&
          (!path.to || this.hasAuthorization(path.to.other(otherSide))))
      }
      if (options.length == 0) {
        options = this.floorplan.paths.filter(path =>
          path.from == door &&
          path.room == room &&
          (!path.to || this.hasAuthorization(path.to.other(room))))
      }
      return options[Math.floor(Math.random() * options.length)]
    } else {
      let options = this.floorplan.paths.filter(path => 
        !path.from && path.to && 
        this.hasAuthorization(path.to.other(path.room)))
      if (options.length == 0) this.path = null
      return options[Math.floor(Math.random() * options.length)]
    }
  }

  private moveOn(path: Path) {
    if (this.path && path && path.room != this.path.room) {
      let door = this.path ? (this.forward ? this.path.to : this.path.from) : null          
      if (door) {
        door.setState('active',200)        
        this.floorplan.verifier.verifyDoorAccess(this,path.room).then((ok) => {
          if (ok.sat && door) {
            door.setState('ok',200)
            this.moving = true
            this.path = path
            this.forward = true
            this.position = 0
          } else if (door) {
            door.setState('ko',500)
            console.log("could not pass door")
            let self = this
            if (!this.timeout) window.setTimeout(() => {
              self.moveOn(self.choosePath())
            },700)
          } else {
            console.error("what?")
          }
        })
      } else {
        console.error("there is no door?")
      }
    } else {
      this.path = path
      this.forward = true
      this.moving = true
      this.position = 0
    }        
  }

  public leave = () => {   
    if (this.timeout) window.clearTimeout(this.timeout)
    this.path = null
    this.moving = false
    this.elem.classList.add("absent")
  }

  public enter = () => {
    this.elem.classList.remove("absent")
    if (!this.path) {
      this.moveOn(this.choosePath())
    }
  }

  public reenter = () => {
    this.leave()
    this.enter()
  }

  public animate = (d: number) => {    
    if (this.moving && this.path) {
      if (this.forward && this.position + d < this.path.length)
        this.position += d
      else if (!this.forward && this.position - d > 0)
        this.position -= d
      else {
        this.position = this.forward ? this.path.length : 0                    
        this.moving = false
        let path = this.choosePath()
        this.moveOn(path)
      }
      let point = this.getPoint()
      this.elem.cx.baseVal.value = point.x
      this.elem.cy.baseVal.value = point.y
    }
  }
}