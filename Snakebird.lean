import Snakebird.Tactics

open Dir

set_option maxHeartbeats 2000000

def level1 :=
•••••••••▦▦•••••◎•••••••
•••••••••▦▦▦▦•••••••••••
•••••▦••••▦▦••••••••••••
•••••••▦••▦•••*•▦•••••••
••••╺━0•••▦•▦•••▦▦•••*••
•▦▦▦▦▦▦▦▦•••▦▦•••••••▦▦•
•▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦•
•▦▦▦▦▦▦▦▦▦•▦▦▦▦▦▦▦▦▦▦▦••
••▦▦▦▦▦▦▦▦••▦▦▦▦▦▦▦▦▦▦••
∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼

#print level1

example : level1.completable := by
  move 0 right
  move 0 right
  move 0 right
  move 0 down
  move 0 right
  move 0 right
  move 0 up
  move 0 up
  move 0 right
  move 0 right
  move 0 right
  /-move 0 down
  move 0 down
  move 0 right
  move 0 right
  move 0 right
  move 0 right
  move 0 right
  move 0 right
  move 0 up 
  move 0 right
  move 0 up 
  move 0 left
  move 0 left
  move 0 left
  move 0 left
  move 0 up 
  move 0 left
  move 0 up 
  move 0 up 
  complete
-/