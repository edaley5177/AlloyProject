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

sig Passages extends RoomConnectors {}
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
	all ra:QuadrilateralRoom, N:Direction, S:Direction, E:Direction, W:Direction | coords.axes[N] = S && coords.axes[E] = W && N!=W && N!=E && #nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]>0 implies nextRoom[E,this,nextRoom[S,this,nextRoom[W,this,nextRoom[N, this, ra]]]] = ra
	
	startRoom in rooms
	endRoom in rooms
	startRoom != endRoom
	all ra:QuadrilateralRoom, rb:QuadrilateralRoom | ra in rb.^(roomOptions[doors, coords])
	all r:QuadrilateralRoom, d:Direction | #((doors+walls).connection[r][d])<=1
	#(roomOptions[walls, coords] & roomOptions[doors, coords]) = 0
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

pred show (m:QuadrilateralMaze) {
	#rooms>=4
 	one Walls
	one Doors
	no Passages
one CoordSet
//	#(walls.connection)> 0
}

pred showa{
	some rooms
	one Walls 
	one CoordSet
//	no Doors
//	no QuadrilateralMaze
//	no Passages
}
run show for 7  but 1 QuadrilateralMaze
