one sig True {}

sig Room {}

abstract sig RoomConnectors {
	connection: Room -> some Direction -> lone Room
} {
	// Symmetry
	roomOptions[] = ~roomOptions[]
	// Nonduplication
	all ra:Room, rb:Room | #(connection[ra].rb) <=1
}
abstract sig AdjacentRoomConnectors extends RoomConnectors {
	coords: one CoordSet
} {
	// Irreflexivity
	all r:Room, d:Direction| connection[r][d] != r
	// All symmetry connections follow the reverse direction
	all r:Room, d:Direction| #(connection[r][d])>0 implies connection[connection[r][d]][(coords.axes)[d]] = r
}

sig Walls extends AdjacentRoomConnectors {}
sig Doors extends AdjacentRoomConnectors {}

sig Direction {}
sig CoordSet {
	directions: set Direction,
	axes: Direction-> lone Direction,
} {
	//Axes defines the relation between opposite directions; (E->W, W->E, etc.)
	all d:Direction| d.axes.axes = d
	no d:Direction| d.axes = d
	//Completeness of the axes mapping
	axes[Direction] = directions
	axes.Direction = directions
}

abstract sig ConnectedMaze {
	coords: one CoordSet,
	startRoom: Room,
	endRoom: Room,
	rooms: set Room,
	walls: one Walls,
	doors: one Doors
} {
//Share coordinate systems between all components
	walls.coords = coords
	doors.coords = coords
//Basic constraints on start/endroom
	startRoom in rooms
	endRoom in rooms
	startRoom != endRoom
//Full maze connectivity
	all ra:Room, rb:Room | ra in rb.^(roomOptions[doors, coords])
	//At most one wall/door between a pair of rooms.
	all r:Room, d:Direction | #((doors+walls).connection[r][d])<=1
	
}

sig QuadrilateralMaze extends ConnectedMaze {
} 
{
	// Impose coordinate system
	#(coords.directions) =4
//Cylcicity constraint; heavy calculation and rarely relevant for test cases. Comment out for quick testing.
	all ra:Room, N:Direction, S:Direction, E:Direction, W:Direction | coords.axes[N] = S && coords.axes[E] = W && N!=W && N!=E && #nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]>0 implies nextRoom[E,this,nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]] = ra
	

}

sig HexagonalMaze extends ConnectedMaze {
} 
{
	#(coords.directions) =6
//Couldn't figure out how to express cyclicity in hexagonal coord system. It's not as straightforward as quadrilateral.
}

sig Heart{}

sig Being{
	currRoom: lone Room,
	healthBar: set Heart,
	maxHP: set Heart
} {
// The set of hearts in healthBar represents current HP. That should be a subset of maxHP.
	healthBar in maxHP
}

abstract sig RoomEffect{
	room: Room,
	enabled: lone True
}

sig HealEffect extends RoomEffect{
	healAmount: set Heart
}

sig DisarmEffect extends RoomEffect {
	target: one RoomEffect
} {
	target != this
}

sig Game{
	player: one Being,
	monsters: set Being,
	maze: one ConnectedMaze,
	effects: set RoomEffect
} {
	player not in monsters
// Players have 5HP in the game
	#(player.maxHP) = 5
// Monsters have 1 HP in this game
	all m:monsters | #(m.maxHP)=1
	#monsters =2
	// Constrain rooms of all entities to be in the maze
	player.currRoom in maze.rooms
	monsters.currRoom in maze.rooms
	effects.room in maze.rooms
// monsters and effects are each 0 or 1 to a room
	all disj a, b : monsters | disj[a.currRoom, b.currRoom]
	all disj a, b : effects | disj[a.room, b.room]
}

fun mazeConn [m:QuadrilateralMaze]: Room -> some Direction -> lone Room {
	m.(doors+walls).connection
}

fun nextRoom [d:Direction, m:QuadrilateralMaze, r:Room]: Room {
	mazeConn[m][r][d]
}

fun roomOptions [rc:RoomConnectors]: Room -> Room {
	{ra:Room, rb:Room|#(ra->Direction->rb & rc.connection)>0}
}

fun roomOptions [rc:RoomConnectors, cs:CoordSet]: Room -> Room {
	{ra:Room, rb:Room|#(ra->cs.directions->rb & rc.connection)>0}
}

assert mazeSolvable {
	all m:ConnectedMaze | m.endRoom in (m.startRoom).^(roomOptions[m.doors, m.coords])
}
assert walldooruniquenedd {
//No wall and door makes the same connection
	all m:ConnectedMaze | #(roomOptions[m.walls, m.coords] & roomOptions[m.doors, m.coords]) = 0
}
pred initialize (g, g':Game) {
	g'.player.maxHP = g.player.maxHP
	g'.player.healthBar = g.player.maxHP
	g'.maze = g.maze
	g'.player.currRoom = g.maze.startRoom
	all m:g.monsters, m':g.monsters | m.currRoom = m'.currRoom implies m.maxHP = m'.maxHP //Each monster has the same maxHP as it previously did
	g.monsters.currRoom = g'.monsters.currRoom // Same number of monsters in the same rooms.
	all b:Being | b in g'.monsters implies b.healthBar = b.maxHP //All monsters are fully healed
	g'.effects.room = g.effects.room
	all e:g'.effects | e.enabled = True
}

pred resolveFights (g, g':Game){
	g.player.currRoom in g.monsters.currRoom implies (#(g'.player.healthBar) = #(g.player.healthBar) - #((currRoom.(g.player.currRoom) - g.player).healthBar)) || (#(g'.player.healthBar) = 0)  //player takes damage equal to the HP of the monsters
	g'.player.currRoom = g.player.currRoom
	g'.player.maxHP = g.player.maxHP
	g'.maze = g.maze
	g'.effects = g.effects
	all m:g.monsters, m':g'.monsters | m.currRoom = m'.currRoom implies m.maxHP = m'.maxHP //Each monster has the same maxHP as it previously did
	g.monsters.currRoom = g'.monsters.currRoom // Same number of monsters in the same rooms.
	all m:g'.monsters |  m.currRoom = g.player.currRoom implies #m.healthBar = 0 // This does kill monsters even if they overkill the player, but... the game is over, so w/e.
}

pred movePlayer (g, g':Game, d:Direction){
	#(g.maze.doors.connection[g.player.currRoom][d])>0 

	g'.player.currRoom = nextRoom[d][g.maze][g.player.currRoom]
	g'.player.maxHP = g.player.maxHP
	g'.player.healthBar = g.player.healthBar

	g'.maze = g.maze
	g'.monsters = g.monsters
	g'.effects = g.effects
}

pred applyEffects (g, g':Game){
	g'.maze = g.maze
	g'.monsters = g.monsters
	
	g'.player.currRoom = g.player.currRoom
	g'.player.maxHP = g.player.maxHP
//Handle disarm effects
	all e, t:g.effects, t':g'.effects | (e.room = g.player.currRoom && e.enabled = True && t'.room = t.room && e.target.room = t'.room) implies t'.enabled = none else t'.enabled = t.enabled
//Handle healing effects
	all e:g.effects, e':g'.effects | (e.room = g.player.currRoom && e.room = e'.room && e.healAmount != none) implies e'.healAmount = e.healAmount && e'.enabled = none && (#(g'.player.healthBar) = #(g.player.healthBar) + #(e.healAmount) || (#(g'.player.healthBar) = #(g.player.maxHP))) else g'.player.healthBar = g.player.healthBar
	g.effects.room = g'.effects.room	

}

pred checkGameEndConditions(g, g':Game){
	#(g.player.healthBar) = 0 || g.player.currRoom = g.maze.endRoom implies initialize[g,g'] else g'=g
}


pred show (m:QuadrilateralMaze) {
	#rooms>=4
 	one Walls
	one Doors
	one CoordSet
	one Game

//	#(walls.connection)> 0
}

pred showInitialize (g:Game, g':Game) {
	initialize[g,g']
	#Game=2
	#(g.player.healthBar) =2 
}
//run show for 7  but 1 QuadrilateralMaze
run showInitialize for 5 but 2 Game

