abstract sig Room {}
sig QuadrilateralRoom extends Room {}

abstract sig RoomConnectors {
	connection: Room ->  one Room
} {
	connection = ~connection
}
abstract sig AdjacentRoomConnectors extends RoomConnectors {} {
	no r:Room| r.connection = r
}
sig Passages extends RoomConnectors {}
sig Walls extends AdjacentRoomConnectors {}
sig Doors extends AdjacentRoomConnectors {}

sig QuadrilateralMaze {
	startRoom: QuadrilateralRoom,
	endRoom: QuadrilateralRoom,
	rooms: set QuadrilateralRoom,
	walls: Walls,
	doors: Doors
} 
{
	all r:QuadrilateralRoom | r.(walls.connection) != r.(doors.connection)
	startRoom in rooms
	endRoom in rooms
	startRoom != endRoom
	endRoom in startRoom.^(doors.connection)
//	all ra:QuadrilateralRoom, rb:QuadrilateralRoom | ra in rb.^(doors.connection)
}

pred show (m:QuadrilateralMaze) {
	some rooms 
 	one Walls
	one Doors
	no Passages
//	#(m.walls.connection) =0
}

run show for 7 but 1 QuadrilateralMaze
