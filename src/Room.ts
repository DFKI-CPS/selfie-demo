class Room {
  public id: string
  public isEntry: boolean  

  private onClick_ = new Publisher<void>()
  public onClick = this.onClick_.expose()

  constructor(
    private elem: SVGElement,
    private floorplan: Floorplan
  ) {
    this.id = elem.id
    this.isEntry = elem.hasAttributeNS('http://dfki.de/cps/selfie', 'is-entry')
    let c: CancellationToken | null = null
    if (!this.isEntry) this.floorplan.onCardSelectionChange.listen((card) => {      
      if (c) c.cancel()
      this.elem.classList.remove('auth','no-auth')
      if (card) {      
        let c1 = card.onAuthorizationAdded.listen((room) => {
          if (room == this) {
            this.elem.classList.remove('no-auth')
            this.elem.classList.add('auth')
          }
        }) 
        let c2 = card.onAuthorizationRemoved.listen((room) => {
          if (room == this) {
            this.elem.classList.remove('auth')
            this.elem.classList.add('no-auth')
          }
        })
        c = CancellationToken.combine(c1,c2)
        this.elem.classList.add(card.hasAuthorization(this) ? 'auth' : 'no-auth')
      }
    })
    elem.addEventListener('click',() => {
      this.onClick_.publish()
    })
  }

  private doors: Door[] | null = null
  public getDoors(): Door[] {
    if (!this.doors)      
      this.doors = this.floorplan.doors.filter(door => door.from == this || door.to == this)
    return this.doors
  } 

  public showError() {
    this.elem.classList.add("ko")
    window.setTimeout(() => this.elem.classList.remove("ko"),500)
  }
}