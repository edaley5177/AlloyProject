abstract sig Room {}
sig QuadrilateralRoom extends Room {}

abstract sig RoomConnectors {
	connection: set Room ->  Room
} {
	connection = ~connection
}
abstract sig AdjacentRoomConnectors extends RoomConnectors {} {
	no r:Room| r in r.connection
}
sig Passages extends RoomConnectors {}
sig Walls extends AdjacentRoomConnectors {}
sig Doors extends AdjacentRoomConnectors {}

sig QuadrilateralMaze {
	startRoom: QuadrilateralRoom,
	endRoom: QuadrilateralRoom,
	rooms: set QuadrilateralRoom,
	walls: one Walls,
	doors: one Doors
} 
{
	all r:QuadrilateralRoom | r.(walls.connection) != r.(doors.connection)
	startRoom in rooms
	endRoom in rooms
	startRoom != endRoom
	endRoom in startRoom.^(doors.connection)
	all ra:QuadrilateralRoom, rb:QuadrilateralRoom | ra in rb.^(doors.connection)
	rooms.((walls+doors).connection) in rooms
	#(walls.connection & doors.connection) = 0
	

}

pred show (m:QuadrilateralMaze) {
#rooms=4
 	one Walls
	one Doors
	no Passages
#(walls.connection)> 0

}

pred showa{
	some rooms
	one Walls 
//	no Doors
//	no QuadrilateralMaze
//	no Passages
}
run show for 5  but 1 QuadrilateralMaze
