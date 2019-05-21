SELFIE Demonstrator
===================

This demonstrator allows you to explore the impact of different points in time
chosen for the verificaiton of a an access control system. The system is 
specified in `model.sysml` and implemented in various files within the `src` 
folder.

Build
-----

To build the system, you need a current TypeScript compiler. There is a 
`tsconfig.json` which tells `tsc` how to compile everything. You just need to 
call `tsc` in the root directory without any command line arguments.

Run
---

The demo can currently only be executed on UNIX based systems (Linux/macOS).
Make sure, the following dependencies are installed on your system and available 
on your `PATH` environment variable:

- **[z3](https://github.com/Z3Prover/z3)** version 4.8.4 or above
- **[websocat](https://github.com/vi/websocat)** version 1.2.0 or above

Then to run the demo, execute `floorplan.sh` and navigate to [localhost:8080](http://localhost:8080)

Controlling the demo
----

The demo as a fixed aspect ratio of 16:9 and is best viewed on a monitor with Full HD or better resolution. 

Some brief instructions:

- Press `+` on your keyboard to add a card
- Press `-` on your keyboard to remove the last added card
- Click a card to show it's access rights
- When a card is selected, click a room to add or remove it from the access rights of the selected card
- When a card is selected, press `+` on your keyboard to add a card with identical access rights
- Press `f` on your keyboard to enter fullscreen
- Click on the reactor or press `e` on your keyboard to trigger an emergency
- Select one of the last three entries for verification. The first two will not do anything and are only for illustrative purposes.

Custom Buildings
----------------

You can draw your own building floorplans as svg files. There is a designated xml namespace (`xmlns:selfie="http://dfki.de/cps/selfie"`) to annotate svg elements such as rooms, doors or motion paths:

- **Rooms** are identified by setting the `class` of an svg element to `"room"` and setting a unique `id`:

  ````xml
  <rect x="10" y="10" width="20" height="10" 
      class="room" id="boiler-room">
  `````
  
  Rooms may be annotated as safe by adding the attribute `selfie:is-entry`

- **Doors** can are identified by `class="door"` and require the annotations `selfie:from` and `selfie:to`:

  ````xml
  <circle cx="10" cy="15" r="4"
          class="door" id="door-001"
          selfie:from="boiler-room"
          selfie:to="outside">
  ````

- **Motion Paths** are paths through the building from one door to another. The paths are required for the visualization. They are annotated with `class="path"`and require the at least one of the annotations `selfie:from` and `selfie:to` pointing to the ids of doors (may be the same door, when a person may move through a room and exit through the door he entered). If either `selfie:from` or `selfie:to` is missing people will randomly spawn on the respective end of the path entering the building. Additionally you must add `selfie:room` pointing to the room the path lies in:

  ````xml
  <path d="M0,0L10,15" class="path"
    selfie:room="outside"
    selfie:to="door-001">
  ````

Note, that there are several additional css classes defined for styling purposes (such as `regular door` or `hatch door`). Please refer to the provided `floorplan.svg` as well as `floorplan.css`. You can safely add styles to `floorplan.css` without affecting the simulation.