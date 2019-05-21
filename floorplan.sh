#!/bin/sh
websocat --text -E\
  ws-l:127.0.0.1:8080 "cmd:z3 model.completion=true -in"\
  --static-file\
    "/:text/html:floorplan.html"\
    "/floorplan.svg:image/svg+xml:floorplan.svg"\
    "/floorplan.css:text/css:floorplan.css"\
    "/floorplan.js:application/ecmascript:floorplan.js"\
    "/floorplan.js.map:text/plain:floorplan.js.map"\
    "/images/logo.svg:image/svg+xml:images/logo.svg"\
    "/images/radioactive.svg:image/svg+xml:images/radioactive.svg"\
    "/images/play.svg:image/svg+xml:images/play.svg"\
    "/images/pause.svg:image/svg+xml:images/pause.svg"\
    "/src/Card.ts:application/typescript:src/Card.ts"\
    "/src/Door.ts:application/typescript:src/Door.ts"\
    "/src/Floorplan.ts:application/typescript:src/Floorplan.ts"\
    "/src/Geometry.ts:application/typescript:src/Geometry.ts"\
    "/src/Main.ts:application/typescript:src/Main.ts"\
    "/src/Path.ts:application/typescript:src/Path.ts"\
    "/src/Room.ts:application/typescript:src/Room.ts"\
    "/src/Rx.ts:application/typescript:src/Rx.ts"\
    "/src/Verifier.ts:application/typescript:src/Verifier.ts"\
