function init() {
  // check whether were running within the svg file
  if (location.pathname.endsWith(".svg")) { 
    // check if the svg is viewed standalone    
    if (!window.parent || window.parent == window) {
      console.log("Detected Standalone SVG")
      let root = document.querySelector('svg')
      if (!root) {
        console.error("could not find svg root node"); return
      }
      let floorplan = initFloorplan(root)      
      console.log(floorplan)
    }
    // TODO
  } else { // assume were wihin the html app    
    console.log("Detected Embedded SVG")
    let obj = document.getElementById('floorplan')
    if (!(obj instanceof HTMLObjectElement)) {
      console.error("the object with id 'floorplan' is missing"); return
    } 
    obj.addEventListener('load',(e) => {
      if (!(obj instanceof HTMLObjectElement)) {
        console.error("the object with id 'floorplan' is missing"); return
      } 
      let svgDoc = obj.contentDocument
      if (!svgDoc) {
        console.error("no content document within the 'floorplan' object"); return
      }    
      let svg = svgDoc.querySelector("svg")
      if (!svg) {
        console.error("no svg within the 'floorplan' object"); return
      }
      let floorplan = initFloorplan(svg)
      initUI(floorplan)
    })
  }
}

function initUI(floorplan: Floorplan) {    
  console.log(floorplan)
  let addButton = document.getElementById('add')
  if (!(addButton instanceof HTMLButtonElement)) {
    console.error("the add button is missing"); return
  }
  floorplan.verifier.onModeChange.listen(mode => {    
    let id: string = ""
    switch(mode) {
      case VerificationMode.PreDeployment: id = "v-pre"; break
      case VerificationMode.Topology: id = "v-top"; break
      case VerificationMode.AccessRights: id = "v-acr"; break
      case VerificationMode.DoorAccess: id = "v-acc"; break
      case VerificationMode.Emergency: id = "v-emg"; break
    }
    let elem = document.getElementById(id)
    if (elem instanceof HTMLInputElement) {
      elem.checked = true
    }
  })
  document.getElementsByName("vtime").forEach(inp => {
    inp.addEventListener('change',() => {
      let selected = document.querySelector('input[name=vtime]:checked')
      if (selected instanceof HTMLInputElement) {
        switch (selected.value) {
          case "pre":
            floorplan.verifier.setMode(VerificationMode.PreDeployment)
            break
          case "top":
            floorplan.verifier.setMode(VerificationMode.Topology)
            break
          case "acr":
            floorplan.verifier.setMode(VerificationMode.AccessRights)
            break  
          case "acc":
            floorplan.verifier.setMode(VerificationMode.DoorAccess)
            break  
          case "emg":
            floorplan.verifier.setMode(VerificationMode.Emergency)
            break
        }        
      }
    })    
  })
  
  let cards: HTMLUListElement = (() => {
    let cards = document.getElementById('cards')
    if (!(cards instanceof HTMLUListElement)) {      
      throw new Error("the card ulist is missing")
    }    
    return cards
  })()
  addButton.addEventListener('click', (e) => {
    let card = floorplan.createCard()
  })  
  floorplan.onCardAdded.listen((card) => {
    let elem = document.createElement('li')
    elem.classList.add('card',"p01")
    elem.textContent = "-"
    elem.style.backgroundColor = card.color    
    cards.appendChild(elem)
    elem.addEventListener("click",() => {
      if (card.isSelected()) card.deselect(); else card.select()
    })
    card.onSelected.listen(() => elem.classList.add("active"))
    card.onDeselected.listen(() => elem.classList.remove("active"))
    card.onRemove.listen(() => cards.removeChild(elem))
  })
  floorplan.onCardCountChange.listen((n) => {
    let i = 1
    while (n > 2 * i * i) i++
    let s = ""
    for (let j = 0; j < i; j++) {
      s += "1fr "
    }
    cards.style.gridTemplateColumns = s
  })
}

function initFloorplan(svg: SVGElement): Floorplan {
  let floorplan = new Floorplan(svg)
  let t0 = 0
  function animationLoop(d: number) {
    floorplan.animate(d - t0)
    t0 = d
    window.requestAnimationFrame(animationLoop)
  }
  window.requestAnimationFrame(animationLoop)  
  let i = 0;
  window.addEventListener("keypress", e => {
    switch (e.key) {
      case '+':
        floorplan.createCard()
        break
      case '-':
        floorplan.removeCard()
        break
      case 'e':
        floorplan.toggleEmergency()
        break
      /*case 'x':
        if (i < floorplan.doors.length + 1) {
          console.log(floorplan.doors[i-1].id)
        }
        break
      case 'd':     
        if (i > 0) {
          floorplan.doors[i-1].endEmergency()
        }         
        if (i < floorplan.doors.length) {
          let door = floorplan.doors[i]          
          door.emergency(Direction.In)
          door.to.showError()
          i++
        }
        break*/
      case 'f':
        let x = window.document.querySelector('svg,body')        
        if (x) {          
          x.requestFullscreen()
        }
        break
      default:
        break
    }
  })
  return floorplan
}

document.addEventListener('DOMContentLoaded',init,{
  once: true
})