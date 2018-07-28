one sig True {}

abstract sig Room {}
sig QuadrilateralRoom extends Room {}

abstract sig RoomConnectors {
	connection: Room -> some Direction -> lone Room
} {
	roomOptions[] = ~roomOptions[]
	all ra:Room, rb:Room | #(connection[ra].rb) <=1
}
abstract sig AdjacentRoomConnectors extends RoomConnectors {
	coords: one CoordSet
} {
	all r:Room, d:Direction| connection[r][d] != r
	all r:Room, d:Direction| #(connection[r][d])>0 implies connection[connection[r][d]][(coords.axes)[d]] = r
}

one sig t {
	ra: Room,
	rb: Room,
	cs:CoordSet,
	d:Direction
} { 
d in cs.directions
Doors.connection[ra][d] = rb}

sig Walls extends AdjacentRoomConnectors {}
sig Doors extends AdjacentRoomConnectors {}

sig Direction {}
sig CoordSet {
	directions: set Direction,
	axes: Direction-> lone Direction,
} {
	all d:Direction| d.axes.axes = d
	no d:Direction| d.axes = d
	axes[Direction] = directions
	axes.Direction = directions
}

sig QuadrilateralMaze {
	coords: one CoordSet,
	startRoom: QuadrilateralRoom,
	endRoom: QuadrilateralRoom,
	rooms: set QuadrilateralRoom,
	walls: one Walls,
	doors: one Doors,
	direction: one Direction
} 
{
	
	#(coords.directions) =4
	walls.coords = coords
	doors.coords = coords
//Cylcicity constraint; heavy calculation and rarely relevant for test cases. Comment out for quick testing.
//	all ra:QuadrilateralRoom, N:Direction, S:Direction, E:Direction, W:Direction | coords.axes[N] = S && coords.axes[E] = W && N!=W && N!=E && #nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]>0 implies nextRoom[E,this,nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]] = ra
	
	startRoom in rooms
	endRoom in rooms
	startRoom != endRoom
	all ra:QuadrilateralRoom, rb:QuadrilateralRoom | ra in rb.^(roomOptions[doors, coords])
	all r:QuadrilateralRoom, d:Direction | #((doors+walls).connection[r][d])<=1
	#(roomOptions[walls, coords] & roomOptions[doors, coords]) = 0
}

sig Heart{}

sig Being{
	//a being can be in a room
	currRoom: lone Room,
	healthBar: set Heart,
	maxHP: set Heart
} {
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

sig DamageEffect extends RoomEffect {
}

sig Game{
	player: one Being,
	monsters: set Being,
	maze: one QuadrilateralMaze,
	effects: set RoomEffect
} {
	player not in monsters
	#(player.maxHP) = 5
	all m:monsters | #(m.maxHP)=1
	#monsters =2
	#(monsters.currRoom) = #(monsters) // 0-1 monsters per room.
	player.currRoom in maze.rooms
	monsters.currRoom in maze.rooms
	effects.room in maze.rooms

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

