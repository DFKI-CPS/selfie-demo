class Path {
  public from: Door | null
  public to: Door | null
  public room: Room
  public length: number

  constructor(
    private elem: SVGPathElement,
    private forward: boolean,
    private floorplan: Floorplan) {
      this.length = elem.getTotalLength()
      let roomId = elem.getAttributeNS('http://dfki.de/cps/selfie','room')
      if (!roomId) throw new Error("attribute 'selfie:room' is not present on path")    
      this.room = floorplan.getRoom(roomId)
      let fromId = elem.getAttributeNS('http://dfki.de/cps/selfie','from')
      let toId = elem.getAttributeNS('http://dfki.de/cps/selfie','to')   
      if (forward) {
        if (fromId) this.from = floorplan.getDoor(fromId)
        if (toId) this.to = floorplan.getDoor(toId)
      } else {
        if (fromId) this.to = floorplan.getDoor(fromId)
        if (toId) this.from = floorplan.getDoor(toId)
      }
    }

  public at(position: number) {
    return this.elem.getPointAtLength(this.forward ? position : this.length - position)
  }
}