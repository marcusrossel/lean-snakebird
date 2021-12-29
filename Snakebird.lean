import Snakebird.Syntax

def test :=
◎••••••|
▦▦▦▦▦▦▦|
▦▦▦••▦•|
∼∼∼∼∼∼∼

def _Debug.get! {α} [Inhabited α] : _Debug α →  α
  | _Debug.value a => a
  | _ => Inhabited.default

def strFromMv : _Debug Game.Move.Result → String 
| Game.Move.Result.success _ => "success"
| Game.Move.Result.failure $ [Game.Move.Error.unknownSnake _] => "unknownSnake"
| Game.Move.Result.failure $ [Game.Move.Error.blockedByRock _] => "blockedByRock"
| Game.Move.Result.failure $ [Game.Move.Error.blockedBySaw   _] => "blockedBySaw"
| Game.Move.Result.failure $ [Game.Move.Error.blockedByWater _] => "blockedByWater"
| Game.Move.Result.failure $ [Game.Move.Error.blockedBySnake _ _] => "blockedBySnake"
| Game.Move.Result.failure $ [Game.Move.Error.fellInWater    _] => "fellInWater"
| Game.Move.Result.failure $ [Game.Move.Error.fellOnSaw      _] => "fellOnSaw"
| _Debug.message m => m
| _ => "Multiple errors"

#eval strFromMv $ test.move ⟨1, Dir.right⟩
#eval test
#eval (test.move ⟨1, Dir.right⟩).get!.getD Inhabited.default

def game :=
•••••••••▦▦•••••◎•••••••|
•••••••••▦▦▦▦•••••••••••|
•••••▦••••▦▦••••••••••••|
•••••••▦••▦•••*•▦•••••••|
••••╺━0•••▦•▦•••▦▦•••*••|
•▦▦▦▦▦▦▦▦•••▦▦•••••••▦▦•|
•▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦•|
•▦▦▦▦▦▦▦▦▦•▦▦▦▦▦▦▦▦▦▦▦••|
••▦▦▦▦▦▦▦▦••▦▦▦▦▦▦▦▦▦▦••|
∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼