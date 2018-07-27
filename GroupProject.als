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
sig heart{}
//a health bar has zero or more hearts
sig healthBar set hearts{
} 
abstract sig Being{
	//a being can be in a room
	currRoom in rooms
	
}
sig Player extends Being{
	//if the number of hearts goes below 1, then the player goes back to the start room
	one healthBar

}
sig Monster extends Being{
	//if the number of hearts goes below 1, then the monster dissapears and never comes back for this generation of the maze
	one healthBar
	one spawnRoom
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
