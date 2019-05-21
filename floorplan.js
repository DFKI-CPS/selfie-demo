var Card = /** @class */ (function () {
    function Card(floorplan) {
        var _this = this;
        this.position = 0;
        this.moving = true;
        this.forward = true;
        this.authorizations = new Set();
        this.timeout = 0;
        this.action = function () { };
        this.selected = false;
        this.onSelected_ = new Publisher();
        this.onSelected = this.onSelected_.expose();
        this.onDeselected_ = new Publisher();
        this.onDeselected = this.onDeselected_.expose();
        this.onReachedDoor_ = new Publisher();
        this.onReachedDoor = this.onReachedDoor_.expose();
        this.onRemove_ = new Publisher();
        this.onRemove = this.onRemove_.expose();
        this.onAuthorizationAdded_ = new Publisher();
        this.onAuthorizationAdded = this.onAuthorizationAdded_.expose();
        this.onAuthorizationRemoved_ = new Publisher();
        this.onAuthorizationRemoved = this.onAuthorizationRemoved_.expose();
        this.addAuthorization = function (room) {
            var wasThere = _this.hasAuthorization(room);
            _this.authorizations.add(room);
            if (!wasThere)
                _this.onAuthorizationAdded_.publish(room);
            if (!_this.path)
                _this.path = _this.choosePath();
        };
        this.choosePath = function () {
            var door = _this.path ? (_this.forward ? _this.path.to : _this.path.from) : null;
            var room = _this.path ? _this.path.room : null;
            if (door && room) {
                var otherSide_1 = door.other(room);
                var options = _this.floorplan.paths.filter(function (path) {
                    return path.from == door &&
                        path.room == otherSide_1 &&
                        path.to != path.from &&
                        _this.hasAuthorization(path.room) &&
                        (!path.to || _this.hasAuthorization(path.to.other(otherSide_1)));
                });
                if (options.length == 0) {
                    options = _this.floorplan.paths.filter(function (path) {
                        return path.from == door &&
                            path.room == otherSide_1 &&
                            _this.hasAuthorization(path.room) &&
                            (!path.to || _this.hasAuthorization(path.to.other(otherSide_1)));
                    });
                }
                if (options.length == 0) {
                    options = _this.floorplan.paths.filter(function (path) {
                        return path.from == door &&
                            path.room == room &&
                            (!path.to || _this.hasAuthorization(path.to.other(room)));
                    });
                }
                return options[Math.floor(Math.random() * options.length)];
            }
            else {
                var options = _this.floorplan.paths.filter(function (path) {
                    return !path.from && path.to &&
                        _this.hasAuthorization(path.to.other(path.room));
                });
                if (options.length == 0)
                    _this.path = null;
                return options[Math.floor(Math.random() * options.length)];
            }
        };
        this.leave = function () {
            if (_this.timeout)
                window.clearTimeout(_this.timeout);
            _this.path = null;
            _this.moving = false;
            _this.elem.classList.add("absent");
        };
        this.enter = function () {
            _this.elem.classList.remove("absent");
            if (!_this.path) {
                _this.moveOn(_this.choosePath());
            }
        };
        this.reenter = function () {
            _this.leave();
            _this.enter();
        };
        this.animate = function (d) {
            if (_this.moving && _this.path) {
                if (_this.forward && _this.position + d < _this.path.length)
                    _this.position += d;
                else if (!_this.forward && _this.position - d > 0)
                    _this.position -= d;
                else {
                    _this.position = _this.forward ? _this.path.length : 0;
                    _this.moving = false;
                    var path = _this.choosePath();
                    _this.moveOn(path);
                }
                var point = _this.getPoint();
                _this.elem.cx.baseVal.value = point.x;
                _this.elem.cy.baseVal.value = point.y;
            }
        };
        this.floorplan = floorplan;
        var h = Math.floor(Math.random() * 360);
        var s = (66 + Math.floor(Math.random() * 20));
        var l = (66 + Math.floor(Math.random() * 20));
        this.color = "hsl(" + h + "," + s + "%," + l + "%)";
        this.elem = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        this.elem.classList.add('person');
        var people = this.floorplan.svg.querySelector('#people');
        if (!people)
            throw new Error("cannot find #people");
        people.appendChild(this.elem);
        this.elem.r.baseVal.value = 4;
        this.elem.style.fill = this.color;
        this.path = this.choosePath();
        this.floorplan.rooms.forEach(function (r) { if (r.isEntry)
            _this.authorizations.add(r); });
    }
    Card.prototype.remove = function () {
        this.deselect();
        this.onRemove_.publish();
        var parent = this.elem.parentNode;
        if (parent)
            parent.removeChild(this.elem);
    };
    Card.prototype.hasAuthorization = function (room) {
        return room.isEntry || this.authorizations.has(room);
    };
    Card.prototype.getRoom = function () {
        if (this.path)
            return this.path.room;
        else {
            var res = this.floorplan.rooms.find(function (r) { return r.isEntry; });
            if (!res)
                throw new Error("could not find an entry");
            return res;
        }
    };
    Card.prototype.getAuthorizations = function () {
        return this.authorizations;
    };
    Card.prototype.removeAuthorization = function (room) {
        if (!room.isEntry) {
            if (this.authorizations["delete"](room))
                this.onAuthorizationRemoved_.publish(room);
        }
    };
    Card.prototype.toggleAuthorization = function (room) {
        if (this.hasAuthorization(room)) {
            this.removeAuthorization(room);
            return false;
        }
        else {
            this.addAuthorization(room);
            return true;
        }
    };
    Card.prototype.getPoint = function () {
        return this.path ? this.path.at(this.position) : new DOMPoint(0, 0);
    };
    Card.prototype.select = function () {
        if (!this.selected) {
            this.elem.classList.add("active");
            this.selected = true;
            this.onSelected_.publish();
        }
    };
    Card.prototype.deselect = function () {
        if (this.selected) {
            this.elem.classList.remove("active");
            this.selected = false;
            this.onDeselected_.publish();
        }
    };
    Card.prototype.isSelected = function () { return this.selected; };
    Card.prototype.moveOn = function (path) {
        var _this = this;
        if (this.path && path && path.room != this.path.room) {
            var door_1 = this.path ? (this.forward ? this.path.to : this.path.from) : null;
            if (door_1) {
                door_1.setState('active', 200);
                this.floorplan.verifier.verifyDoorAccess(this, path.room).then(function (ok) {
                    if (ok.sat && door_1) {
                        door_1.setState('ok', 200);
                        _this.moving = true;
                        _this.path = path;
                        _this.forward = true;
                        _this.position = 0;
                    }
                    else if (door_1) {
                        door_1.setState('ko', 500);
                        console.log("could not pass door");
                        var self_1 = _this;
                        if (!_this.timeout)
                            window.setTimeout(function () {
                                self_1.moveOn(self_1.choosePath());
                            }, 700);
                    }
                    else {
                        console.error("what?");
                    }
                });
            }
            else {
                console.error("there is no door?");
            }
        }
        else {
            this.path = path;
            this.forward = true;
            this.moving = true;
            this.position = 0;
        }
    };
    return Card;
}());
var Direction;
(function (Direction) {
    Direction[Direction["In"] = 0] = "In";
    Direction[Direction["Out"] = 1] = "Out";
})(Direction || (Direction = {}));
var Door = /** @class */ (function () {
    function Door(elem, floorplan) {
        var _this = this;
        this.elem = elem;
        this.floorplan = floorplan;
        this.reset = function () {
            _this.state = _this.initialState.slice();
            _this.updateState();
        };
        this.updateState = function () {
            if (!_this.floorplan.isEmergency()) {
                _this.state.forEach(function (s) {
                    if (!_this.elem.classList.contains(s))
                        _this.elem.classList.add(s);
                });
                _this.elem.classList.forEach(function (s) {
                    if (_this.state.indexOf(s) < 0)
                        _this.elem.classList.remove(s);
                });
            }
        };
        this.setState = function (state, timeout) {
            _this.state.push(state);
            _this.updateState();
            var removed = false;
            var remove = function () {
                if (!removed) {
                    var i = _this.state.indexOf(state);
                    if (i >= 0)
                        _this.state.splice(_this.state.indexOf(state), 1);
                    removed = true;
                    _this.updateState();
                }
            };
            if (timeout)
                window.setTimeout(remove, timeout);
            return {
                cancel: remove
            };
        };
        this.id = elem.id;
        var fromId = elem.getAttributeNS('http://dfki.de/cps/selfie', 'from');
        if (!fromId)
            throw new Error("attribute 'selfie:from' is missing on door");
        var toId = elem.getAttributeNS('http://dfki.de/cps/selfie', 'to');
        if (!toId)
            throw new Error("attribute 'selfie:to' is missing on door");
        this.from = floorplan.getRoom(fromId);
        this.to = floorplan.getRoom(toId);
        this.initialState = [];
        elem.classList.forEach(function (e) { return _this.initialState.push(e); });
        this.state = this.initialState.slice();
        this.arrow = document.createElementNS("http://www.w3.org/2000/svg", "line");
        this.arrow.classList.add("arrow");
        var rect = this.elem.getBBox();
        if (rect.width == 0) {
            this.arrow.y1.baseVal.value = rect.y + rect.height / 2;
            this.arrow.y2.baseVal.value = rect.y + rect.height / 2;
            this.arrow.x1.baseVal.value = rect.x - 8;
            this.arrow.x2.baseVal.value = rect.x + 8;
        }
        else if (rect.height == 0) {
            this.arrow.x1.baseVal.value = rect.x + rect.width / 2;
            this.arrow.x2.baseVal.value = rect.x + rect.width / 2;
            this.arrow.y1.baseVal.value = rect.y - 8;
            this.arrow.y2.baseVal.value = rect.y + 8;
        }
        else {
            this.arrow.x1.baseVal.value = rect.x + rect.width / 2;
            this.arrow.x2.baseVal.value = rect.x + rect.width / 2;
            this.arrow.y1.baseVal.value = rect.y + rect.height / 2 - 8;
            this.arrow.y2.baseVal.value = rect.y + rect.height / 2 + 8;
        }
    }
    Door.prototype.other = function (room) {
        var rid = typeof (room) == "string" ? room : room.id;
        if (rid == this.from.id)
            return this.to;
        else if (rid == this.to.id)
            return this.from;
        else
            throw new Error("the room is not connected to this door");
    };
    Door.prototype.emergency = function (dir) {
        this.state = this.initialState.slice();
        if (dir == Direction.In) {
            this.elem.classList.add("open", "in");
            this.arrow.classList.add("open", "in");
        }
        else if (dir == Direction.Out) {
            this.elem.classList.add("open", "out");
            this.arrow.classList.add("open", "out");
        }
        else
            this.elem.classList.add("close");
        this.arrow.classList.add("close");
    };
    Door.prototype.endEmergency = function () {
        this.arrow.classList.remove("open", "in", "out", "close");
        this.updateState();
    };
    return Door;
}());
var Floorplan = /** @class */ (function () {
    function Floorplan(svg) {
        var _this = this;
        this.svg = svg;
        this.rooms = [];
        this.doors = [];
        this.paths = [];
        this.cards = [];
        this.verifier = new Verifier(this, "ws://127.0.0.1:8080");
        this.speed = 0.08;
        this.emergency = false;
        this.onCardAdded_ = new Publisher();
        this.onCardAdded = this.onCardAdded_.expose();
        this.onCardCountChange_ = new Publisher();
        this.onCardCountChange = this.onCardCountChange_.expose();
        this.cardSelection = null;
        this.onCardSelectionChange_ = new Publisher();
        this.onCardSelectionChange = this.onCardSelectionChange_.expose();
        this.cancelEmergency = CancellationToken.noop();
        svg.querySelectorAll('.room').forEach(function (elem) {
            _this.addRoom(new Room(elem, _this));
        });
        var escapePlan = svg.querySelector("#escapePlan");
        svg.querySelectorAll('.door').forEach(function (elem) {
            var door = new Door(elem, _this);
            _this.addDoor(door);
            if (!escapePlan)
                throw new Error("no escape plan");
            escapePlan.appendChild(door.arrow);
        });
        svg.querySelectorAll('.path').forEach(function (elem) {
            _this.addPath(new Path(elem, true, _this));
            _this.addPath(new Path(elem, false, _this));
        });
        this.reactor = (function () {
            var r = svg.querySelector('#reactor');
            if (!r)
                throw new Error("reactor is missing");
            else
                return r;
        })();
        this.reactor.addEventListener('click', function () { return _this.toggleEmergency(); });
        this.verifier.onModeChange.listen(function (mode) {
            if (mode < VerificationMode.DoorAccess) {
                _this.cards.forEach(function (card) { return card.leave(); });
            }
            else {
                _this.cards.forEach(function (card) { return card.enter(); });
            }
        });
        var indicatorTimeout = null;
        this.verifier.onStateChange.listen(function (verifing) {
            if (indicatorTimeout) {
                window.clearTimeout(indicatorTimeout);
                indicatorTimeout = null;
            }
            if (verifing) {
                indicatorTimeout = window.setTimeout(function () {
                    return svg.querySelectorAll("#indicator").forEach(function (indicator) { return indicator.classList.add("visible"); });
                }, 500);
            }
            else
                svg.querySelectorAll("#indicator").forEach(function (indicator) { return indicator.classList.remove("visible"); });
        });
        this.rooms.forEach(function (room) {
            var entries = _this.doors.filter(function (door) { return door.from == room || door.to == room; });
            var _loop_1 = function (a) {
                var _loop_2 = function (b) {
                    var p = _this.paths.find(function (path) {
                        return path.room == room &&
                            (path.from == entries[a] &&
                                path.to == entries[b] ||
                                path.from == entries[b] &&
                                    path.to == entries[a]);
                    });
                    if (!p)
                        console.warn("No path for " + entries[a].id + "-[" + room.id + "]-" + entries[b].id);
                };
                for (var b = a + 1; b < entries.length; b++) {
                    _loop_2(b);
                }
            };
            for (var a = 0; a < entries.length; a++) {
                _loop_1(a);
            }
        });
    }
    Floorplan.prototype.getSelectedCard = function () { return this.cardSelection; };
    Floorplan.prototype.getRoom = function (id) {
        var result = this.rooms.find(function (room) { return room.id == id; });
        if (!result)
            throw new Error("room '" + id + "' does not exist");
        return result;
    };
    Floorplan.prototype.getDoor = function (id) {
        var result = this.doors.find(function (door) { return door.id == id; });
        if (!result)
            throw new Error("door '" + id + "' does not exist");
        return result;
    };
    Floorplan.prototype.getPathsFrom = function (door) {
        return this.paths.filter(function (path) { return path.from && path.from.id == door; });
    };
    Floorplan.prototype.getPathsTo = function (door) {
        return this.paths.filter(function (path) { return path.to && path.to.id == door; });
    };
    Floorplan.prototype.addRoom = function (room) {
        var _this = this;
        this.rooms.push(room);
        room.onClick.listen(function () {
            if (_this.cardSelection) {
                var card_1 = _this.cardSelection;
                _this.verifier.verifyAccessRights(_this.cardSelection, room).then(function (ok) {
                    console.log(ok);
                    if (!ok.sat) {
                        card_1.toggleAuthorization(room);
                    }
                    else {
                        room.showError();
                    }
                });
            }
        });
    };
    Floorplan.prototype.addDoor = function (door) {
        this.doors.push(door);
    };
    Floorplan.prototype.addPath = function (path) {
        this.paths.push(path);
    };
    Floorplan.prototype.toggleEmergency = function () {
        var _this = this;
        this.emergency = !this.emergency;
        if (this.emergency) {
            this.reactor.classList.add("emergency");
            this.verifier.getEscapePlan().then(function (res) {
                console.log(res);
                _this.doors.map(function (door) {
                    if (res.model.get(door.id + ".fromTo") == true)
                        door.emergency(Direction.In);
                    else if (res.model.get(door.id + ".toFrom") == true)
                        door.emergency(Direction.Out);
                    else
                        door.emergency();
                });
            });
            this.svg.classList.add("emergency");
        }
        else {
            this.reactor.classList.remove("emergency");
            this.svg.classList.remove("emergency");
            this.cards.forEach(function (card) { return card.reenter(); });
            this.doors.forEach(function (door) { return door.reset(); });
            this.doors.forEach(function (door) { return door.endEmergency(); });
        }
        return (this.emergency);
    };
    Floorplan.prototype.isEmergency = function () {
        return this.emergency;
    };
    Floorplan.prototype.createCard = function () {
        var _this = this;
        var card = new Card(this);
        this.cards.push(card);
        if (this.cardSelection) {
            this.cardSelection.getAuthorizations().forEach(function (room) {
                card.addAuthorization(room);
            });
        }
        card.onSelected.listen(function () {
            _this.cardSelection = card;
            _this.onCardSelectionChange_.publish(card);
            _this.cards.forEach(function (card2) {
                if (card2 != card)
                    card2.deselect();
            });
        });
        card.onDeselected.listen(function () {
            if (_this.cardSelection == card) {
                _this.cardSelection = null;
                _this.onCardSelectionChange_.publish(null);
            }
        });
        /*card.onAuthorizationAdded.listen(() => {
          if (this.verifier.getMode() == VerificationMode.AccessRights) this.verifier.verify()
        })
        card.onAuthorizationRemoved.listen(() => {
          if (this.verifier.getMode() == VerificationMode.AccessRights) this.verifier.verify()
        })*/
        var c = card.onRemove.listen(function () {
            _this.cards.splice(_this.cards.indexOf(card), 1);
            c.cancel();
            _this.onCardCountChange_.publish(_this.cards.length);
        });
        this.onCardAdded_.publish(card);
        this.onCardCountChange_.publish(this.cards.length);
    };
    Floorplan.prototype.removeCard = function (card) {
        if (!card) {
            card = this.cards[this.cards.length - 1];
        }
        card.remove();
    };
    Floorplan.prototype.animate = function (dt) {
        var _this = this;
        if (this.emergency) {
        }
        else {
            this.cards.forEach(function (card) { return card.animate(dt * _this.speed); });
        }
    };
    return Floorplan;
}());
function init() {
    // check whether were running within the svg file
    if (location.pathname.endsWith(".svg")) {
        // check if the svg is viewed standalone    
        if (!window.parent || window.parent == window) {
            console.log("Detected Standalone SVG");
            var root = document.querySelector('svg');
            if (!root) {
                console.error("could not find svg root node");
                return;
            }
            var floorplan = initFloorplan(root);
            console.log(floorplan);
        }
        // TODO
    }
    else { // assume were wihin the html app    
        console.log("Detected Embedded SVG");
        var obj_1 = document.getElementById('floorplan');
        if (!(obj_1 instanceof HTMLObjectElement)) {
            console.error("the object with id 'floorplan' is missing");
            return;
        }
        obj_1.addEventListener('load', function (e) {
            if (!(obj_1 instanceof HTMLObjectElement)) {
                console.error("the object with id 'floorplan' is missing");
                return;
            }
            var svgDoc = obj_1.contentDocument;
            if (!svgDoc) {
                console.error("no content document within the 'floorplan' object");
                return;
            }
            var svg = svgDoc.querySelector("svg");
            if (!svg) {
                console.error("no svg within the 'floorplan' object");
                return;
            }
            var floorplan = initFloorplan(svg);
            initUI(floorplan);
        });
    }
}
function initUI(floorplan) {
    console.log(floorplan);
    var addButton = document.getElementById('add');
    if (!(addButton instanceof HTMLButtonElement)) {
        console.error("the add button is missing");
        return;
    }
    floorplan.verifier.onModeChange.listen(function (mode) {
        var id = "";
        switch (mode) {
            case VerificationMode.PreDeployment:
                id = "v-pre";
                break;
            case VerificationMode.Topology:
                id = "v-top";
                break;
            case VerificationMode.AccessRights:
                id = "v-acr";
                break;
            case VerificationMode.DoorAccess:
                id = "v-acc";
                break;
            case VerificationMode.Emergency:
                id = "v-emg";
                break;
        }
        var elem = document.getElementById(id);
        if (elem instanceof HTMLInputElement) {
            elem.checked = true;
        }
    });
    document.getElementsByName("vtime").forEach(function (inp) {
        inp.addEventListener('change', function () {
            var selected = document.querySelector('input[name=vtime]:checked');
            if (selected instanceof HTMLInputElement) {
                switch (selected.value) {
                    case "pre":
                        floorplan.verifier.setMode(VerificationMode.PreDeployment);
                        break;
                    case "top":
                        floorplan.verifier.setMode(VerificationMode.Topology);
                        break;
                    case "acr":
                        floorplan.verifier.setMode(VerificationMode.AccessRights);
                        break;
                    case "acc":
                        floorplan.verifier.setMode(VerificationMode.DoorAccess);
                        break;
                    case "emg":
                        floorplan.verifier.setMode(VerificationMode.Emergency);
                        break;
                }
            }
        });
    });
    var cards = (function () {
        var cards = document.getElementById('cards');
        if (!(cards instanceof HTMLUListElement)) {
            throw new Error("the card ulist is missing");
        }
        return cards;
    })();
    addButton.addEventListener('click', function (e) {
        var card = floorplan.createCard();
    });
    floorplan.onCardAdded.listen(function (card) {
        var elem = document.createElement('li');
        elem.classList.add('card', "p01");
        elem.textContent = "-";
        elem.style.backgroundColor = card.color;
        cards.appendChild(elem);
        elem.addEventListener("click", function () {
            if (card.isSelected())
                card.deselect();
            else
                card.select();
        });
        card.onSelected.listen(function () { return elem.classList.add("active"); });
        card.onDeselected.listen(function () { return elem.classList.remove("active"); });
        card.onRemove.listen(function () { return cards.removeChild(elem); });
    });
    floorplan.onCardCountChange.listen(function (n) {
        var i = 1;
        while (n > 2 * i * i)
            i++;
        var s = "";
        for (var j = 0; j < i; j++) {
            s += "1fr ";
        }
        cards.style.gridTemplateColumns = s;
    });
}
function initFloorplan(svg) {
    var floorplan = new Floorplan(svg);
    var t0 = 0;
    function animationLoop(d) {
        floorplan.animate(d - t0);
        t0 = d;
        window.requestAnimationFrame(animationLoop);
    }
    window.requestAnimationFrame(animationLoop);
    var i = 0;
    window.addEventListener("keypress", function (e) {
        switch (e.key) {
            case '+':
                floorplan.createCard();
                break;
            case '-':
                floorplan.removeCard();
                break;
            case 'e':
                floorplan.toggleEmergency();
                break;
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
                var x = window.document.querySelector('svg,body');
                if (x) {
                    x.requestFullscreen();
                }
                break;
            default:
                break;
        }
    });
    return floorplan;
}
document.addEventListener('DOMContentLoaded', init, {
    once: true
});
var Path = /** @class */ (function () {
    function Path(elem, forward, floorplan) {
        this.elem = elem;
        this.forward = forward;
        this.floorplan = floorplan;
        this.length = elem.getTotalLength();
        var roomId = elem.getAttributeNS('http://dfki.de/cps/selfie', 'room');
        if (!roomId)
            throw new Error("attribute 'selfie:room' is not present on path");
        this.room = floorplan.getRoom(roomId);
        var fromId = elem.getAttributeNS('http://dfki.de/cps/selfie', 'from');
        var toId = elem.getAttributeNS('http://dfki.de/cps/selfie', 'to');
        if (forward) {
            if (fromId)
                this.from = floorplan.getDoor(fromId);
            if (toId)
                this.to = floorplan.getDoor(toId);
        }
        else {
            if (fromId)
                this.to = floorplan.getDoor(fromId);
            if (toId)
                this.from = floorplan.getDoor(toId);
        }
    }
    Path.prototype.at = function (position) {
        return this.elem.getPointAtLength(this.forward ? position : this.length - position);
    };
    return Path;
}());
var Room = /** @class */ (function () {
    function Room(elem, floorplan) {
        var _this = this;
        this.elem = elem;
        this.floorplan = floorplan;
        this.onClick_ = new Publisher();
        this.onClick = this.onClick_.expose();
        this.doors = null;
        this.id = elem.id;
        this.isEntry = elem.hasAttributeNS('http://dfki.de/cps/selfie', 'is-entry');
        var c = null;
        if (!this.isEntry)
            this.floorplan.onCardSelectionChange.listen(function (card) {
                if (c)
                    c.cancel();
                _this.elem.classList.remove('auth', 'no-auth');
                if (card) {
                    var c1 = card.onAuthorizationAdded.listen(function (room) {
                        if (room == _this) {
                            _this.elem.classList.remove('no-auth');
                            _this.elem.classList.add('auth');
                        }
                    });
                    var c2 = card.onAuthorizationRemoved.listen(function (room) {
                        if (room == _this) {
                            _this.elem.classList.remove('auth');
                            _this.elem.classList.add('no-auth');
                        }
                    });
                    c = CancellationToken.combine(c1, c2);
                    _this.elem.classList.add(card.hasAuthorization(_this) ? 'auth' : 'no-auth');
                }
            });
        elem.addEventListener('click', function () {
            _this.onClick_.publish();
        });
    }
    Room.prototype.getDoors = function () {
        var _this = this;
        if (!this.doors)
            this.doors = this.floorplan.doors.filter(function (door) { return door.from == _this || door.to == _this; });
        return this.doors;
    };
    Room.prototype.showError = function () {
        var _this = this;
        this.elem.classList.add("ko");
        window.setTimeout(function () { return _this.elem.classList.remove("ko"); }, 500);
    };
    return Room;
}());
var CancellationToken = /** @class */ (function () {
    function CancellationToken() {
    }
    CancellationToken.combine = function () {
        var tokens = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            tokens[_i] = arguments[_i];
        }
        return {
            cancel: function () { return tokens.forEach(function (t) { return t.cancel(); }); }
        };
    };
    CancellationToken.noop = function () {
        return {
            cancel: function () { }
        };
    };
    return CancellationToken;
}());
var Publisher = /** @class */ (function () {
    function Publisher(queue) {
        this.handlers = [];
        this.queue = queue ? queue : false;
    }
    Publisher.prototype.listen = function (handler) {
        var _this = this;
        this.handlers.push(handler);
        return {
            cancel: function () { return _this.handlers = _this.handlers.filter(function (h) { return h !== handler; }); }
        };
    };
    Publisher.prototype.publish = function (data) {
        if (this.queue)
            this.handlers.splice(0, 1).forEach(function (h) { return h(data); });
        else
            this.handlers.slice(0).forEach(function (h) { return h(data); });
    };
    Publisher.prototype.expose = function () {
        return this;
    };
    return Publisher;
}());
var VerificationMode;
(function (VerificationMode) {
    VerificationMode[VerificationMode["PreDeployment"] = 0] = "PreDeployment";
    VerificationMode[VerificationMode["Topology"] = 1] = "Topology";
    VerificationMode[VerificationMode["AccessRights"] = 2] = "AccessRights";
    VerificationMode[VerificationMode["DoorAccess"] = 3] = "DoorAccess";
    VerificationMode[VerificationMode["Emergency"] = 4] = "Emergency";
})(VerificationMode || (VerificationMode = {}));
var VerifierResult = /** @class */ (function () {
    function VerifierResult(sat) {
        this.sat = null;
        this.model = new Map();
        if (sat)
            this.sat = sat;
    }
    return VerifierResult;
}());
var Verifier = /** @class */ (function () {
    function Verifier(floorplan, url) {
        this.floorplan = floorplan;
        this.url = url;
        this.mode = VerificationMode.DoorAccess;
        this.result = new VerifierResult();
        this.onModeChange_ = new Publisher();
        this.onModeChange = this.onModeChange_.expose();
        this.onStateChange_ = new Publisher();
        this.onStateChange = this.onStateChange_.expose();
        this.staticVariables = [];
        this.staticAssertions = [];
        this.resets = [];
        this.scheduled = [];
    }
    Verifier.prototype.setMode = function (mode) {
        if (mode != this.mode) {
            this.mode = mode;
            this.onModeChange_.publish(mode);
        }
    };
    Verifier.prototype.getMode = function () {
        return this.mode;
    };
    Verifier.prototype.schedule = function (lines) {
        var _this = this;
        if (this.resets.length > 0)
            this.scheduled.push(lines);
        else {
            window.setTimeout(function () {
                _this.onStateChange_.publish(true);
                _this.socket.send("(push)");
                lines().forEach(function (line) { return _this.socket.send(line); });
                _this.socket.send('(pop)');
                _this.socket.send("(echo \"reset\")");
            }, 0);
        }
        return new Promise(function (resolve, reject) { return _this.resets.push(resolve); });
    };
    Verifier.prototype.initStatic = function () {
        var _this = this;
        this.floorplan.doors.forEach(function (door) {
            _this.staticVariables.push({
                name: door.id + ".fromTo",
                type: "Bool"
            }, {
                name: door.id + ".toFrom",
                type: "Bool"
            });
            _this.staticAssertions.push("(not (and " + door.id + ".fromTo " + door.id + ".toFrom))");
        });
    };
    Verifier.prototype.safetyProperty = function (people) {
        var _this = this;
        var variables = this.staticVariables.slice(0);
        var assertions = this.staticAssertions.slice(0);
        people.forEach(function (person, i) {
            _this.floorplan.rooms.forEach(function (room) {
                variables.push({
                    name: room.id + ".card-" + i + ".hasAccess",
                    type: "Bool"
                });
                if (!person.authorisations.has(room))
                    assertions.push("(not " + room.id + ".card-" + i + ".hasAccess)");
                var entries = _this.floorplan.doors
                    .filter(function (door) { return door.from == room || door.to == room; })
                    .map(function (door) {
                    if (door.from == room)
                        return "(and " + door.to.id + ".card-" + i + ".hasAccess " + door.id + ".toFrom)";
                    else
                        return "(and " + door.from.id + ".card-" + i + ".hasAccess " + door.id + ".fromTo)";
                });
                assertions.push("(= " + room.id + ".card-" + i + ".hasAccess (or (= card-" + i + " " + room.id + ") " + entries.join(" ") + "))");
            });
            var exits = _this.floorplan.rooms
                .filter(function (room) { return room.isEntry; })
                .map(function (room) { return room.id + ".card-" + i + ".hasAccess"; });
            assertions.push("(or " + exits.join(" ") + ")");
        });
        // exists card positions -> not exists door combination
        return {
            variables: variables,
            assertions: assertions
        };
    };
    Verifier.prototype.verifyAccessRights = function (card_, room_) {
        var _this = this;
        if (this.mode == VerificationMode.AccessRights) {
            return this.schedule(function () {
                var lines = [];
                var z3 = function (line) {
                    lines.push(line);
                };
                _this.floorplan.cards.forEach(function (card, i) {
                    z3("(declare-const card-" + i + " Int)");
                    var auths = new Set(card.getAuthorizations().values());
                    if (card == card_) {
                        if (auths.has(room_))
                            auths["delete"](room_);
                        else
                            auths.add(room_);
                    }
                    var options = Array.from(auths).map(function (room) { return "(= card-" + i + " " + room.id + ")"; });
                    z3("(assert (or " + options.join(" ") + "))");
                });
                var prop = _this.safetyProperty(_this.floorplan.cards.map(function (card, i) {
                    var auths = new Set(card.getAuthorizations().values());
                    if (card == card_) {
                        if (auths.has(room_))
                            auths["delete"](room_);
                        else
                            auths.add(room_);
                    }
                    return {
                        index: i,
                        authorisations: auths
                    };
                }));
                var vars = prop.variables.map(function (variable) { return "(" + variable.name + " " + variable.type + ")"; });
                console.log(vars);
                z3("(assert (not (exists (" + vars.join(' ') + ") (and " + prop.assertions.join(' ') + "))))");
                z3("(check-sat)");
                _this.floorplan.cards.forEach(function (card, i) {
                    z3("(echo \"card-" + i + ":\")");
                    z3("(eval card-" + i + " :completion true)");
                });
                console.log(lines);
                return lines;
            });
        }
        else {
            return Promise.resolve(new VerifierResult(false));
        }
    };
    Verifier.prototype.verifyDoorAccess = function (card_, room_) {
        var _this = this;
        if (this.mode == VerificationMode.DoorAccess) {
            return this.schedule(function () {
                var lines = [];
                var z3 = function (line) {
                    lines.push(line);
                };
                _this.floorplan.cards.forEach(function (card, i) {
                    var room = card == card_ ? room_ : card.getRoom();
                    z3("(define-fun card-" + i + " () Int " + room.id + ")");
                });
                var prop = _this.safetyProperty(_this.floorplan.cards.map(function (card, i) {
                    return {
                        index: i,
                        authorisations: card.getAuthorizations()
                    };
                }));
                prop.variables.forEach(function (variable) {
                    z3("(declare-const " + variable.name + " " + variable.type + ")");
                });
                prop.assertions.forEach(function (assertion) {
                    z3("(assert " + assertion + ")");
                });
                z3("(check-sat)");
                return lines;
            });
        }
        else {
            return Promise.resolve(new VerifierResult(true));
        }
    };
    Verifier.prototype.getEscapePlan = function () {
        var _this = this;
        return (this.schedule(function () {
            var lines = [];
            var z3 = function (line) {
                lines.push(line);
            };
            _this.floorplan.cards.forEach(function (card, i) {
                z3("(define-fun card-" + i + " () Int " + card.getRoom().id + ")");
            });
            var prop = _this.safetyProperty(_this.floorplan.cards.map(function (card, i) {
                return {
                    index: i,
                    authorisations: card.getAuthorizations()
                };
            }));
            prop.variables.forEach(function (variable) {
                z3("(declare-const " + variable.name + " " + variable.type + ")");
            });
            prop.assertions.forEach(function (assertion) {
                z3("(assert " + assertion + ")");
            });
            z3("(check-sat)");
            _this.floorplan.doors.forEach(function (door) {
                z3("(echo \"" + door.id + ".fromTo:\")");
                z3("(eval " + door.id + ".fromTo :completion true)");
                z3("(echo \"" + door.id + ".toFrom:\")");
                z3("(eval " + door.id + ".toFrom :completion true)");
            });
            return lines;
        }));
    };
    return Verifier;
}());
//# sourceMappingURL=floorplan.js.map