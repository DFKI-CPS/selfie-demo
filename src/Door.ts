enum Direction {
  In,
  Out
}

class Door {
  public id: string
  public from: Room
  public to: Room

  private state: string[]
  private initialState: string[]
  public arrow: SVGLineElement

  constructor(
    private elem: SVGGraphicsElement,
    private floorplan: Floorplan
  ) {
    this.id = elem.id
    let fromId = elem.getAttributeNS('http://dfki.de/cps/selfie','from')
    if (!fromId) throw new Error("attribute 'selfie:from' is missing on door")
    let toId = elem.getAttributeNS('http://dfki.de/cps/selfie','to')
    if (!toId) throw new Error("attribute 'selfie:to' is missing on door")
    this.from = floorplan.getRoom(fromId)
    this.to = floorplan.getRoom(toId)    
    this.initialState = []
    elem.classList.forEach(e => this.initialState.push(e))
    this.state = this.initialState.slice()
    this.arrow = document.createElementNS("http://www.w3.org/2000/svg","line")    
    this.arrow.classList.add("arrow")
    let rect = this.elem.getBBox()
    if (rect.width == 0) {
      this.arrow.y1.baseVal.value = rect.y + rect.height / 2
      this.arrow.y2.baseVal.value = rect.y + rect.height / 2
      this.arrow.x1.baseVal.value = rect.x - 8
      this.arrow.x2.baseVal.value = rect.x + 8
    } else if (rect.height == 0) {
      this.arrow.x1.baseVal.value = rect.x + rect.width / 2
      this.arrow.x2.baseVal.value = rect.x + rect.width / 2
      this.arrow.y1.baseVal.value = rect.y - 8
      this.arrow.y2.baseVal.value = rect.y + 8
    } else {
      this.arrow.x1.baseVal.value = rect.x + rect.width / 2
      this.arrow.x2.baseVal.value = rect.x + rect.width / 2
      this.arrow.y1.baseVal.value = rect.y + rect.height / 2 - 8
      this.arrow.y2.baseVal.value = rect.y + rect.height / 2 + 8
    }    
  }

  public other(room: Room | string): Room {
    let rid = typeof(room) == "string" ? room : room.id 
    if (rid == this.from.id) 
      return this.to
    else if (rid == this.to.id)
      return this.from
    else
      throw new Error("the room is not connected to this door")
  }

  public reset = () => {
    this.state = this.initialState.slice()
    this.updateState()
  }

  public updateState = () => {
    if (!this.floorplan.isEmergency()) {
      this.state.forEach(s => {
        if (!this.elem.classList.contains(s))
          this.elem.classList.add(s)
      })
      this.elem.classList.forEach(s => {
        if (this.state.indexOf(s) < 0)
          this.elem.classList.remove(s)
      })
    }
  }

  public setState = (state: string, timeout?: number) => {
    this.state.push(state)
    this.updateState()
    let removed = false
    let remove = () => { if (!removed) {
      let i = this.state.indexOf(state)
      if (i >= 0) this.state.splice(this.state.indexOf(state),1)
      removed = true
      this.updateState()
    } }
    if (timeout) window.setTimeout(remove,timeout)
    return {
      cancel: remove
    }
  }
  


  public emergency(dir?: Direction) {
    this.state = this.initialState.slice()
    if (dir == Direction.In) {
      this.elem.classList.add("open", "in")
      this.arrow.classList.add("open", "in")      
    } else if (dir == Direction.Out) {
      this.elem.classList.add("open", "out")
      this.arrow.classList.add("open", "out")
    } else
      this.elem.classList.add("close")
      this.arrow.classList.add("close")
  }

  public endEmergency() {
    this.arrow.classList.remove("open","in","out","close")
    this.updateState()
  }
}