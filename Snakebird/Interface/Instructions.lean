namespace Instructions

def instructionText := "Your goal in Snakebird is to move all of the snakebirds to the goal portal.\nBut be careful, there are all kinds of dangers looming: \nYou might fall into the water, fall on a saw,\nor simply navigate yourself into a situation you can't get out of.\nIf you're lucky, you might encounter some fruit.\nIf a snakebird eats a piece of fruit it grows one field longer.\nIn fact, you better get all the fruit you can, or else the goal portal won't open.\nSometimes you'll need to help more than one snakebird reach the goal.\nSnakebirds can push each other around and climb onto each other.\n"

def fieldOverview := "Here's an overview of the different kinds of fields you will encounter:\n\n  ▦ : This is a rock - you can stand on this.\n  ✸ : This is a saw - you can't stand on this.\n  ~ : Water is only found at the very bottom of each level.\n      Make sure you don't fall into it.\n  * : This is a peice of fruit - obviously.\n  ◍ : This is the goal portal when it's locked.\n      Collect all the fruit in a level to open it.\n  ◎ : This is the goal portal when it's open.\n      Each snakebird's head has to touch this to complete a level.\n0━╸ : This is a snakebird. Each snakebird is identified\n      by the number which represents its head."

def credits := "\nThis game is based on a game that already exists, surprisingly called \"Snakebird\".\nIf you want a better UI, I recommend you check it out:\n\nSteam:   https://store.steampowered.com/app/357300/Snakebird/\niOS:     https://apps.apple.com/de/app/snakebird/id1087075743\nAndroid: https://play.google.com/store/apps/details?id=com.NoumenonGames.SnakeBird_Touch&hl=en&gl=US"

partial def instructions : IO Unit := do
  dbg_trace ← IO.Process.run { cmd := "clear" }
  IO.println "Instructions\n"
  IO.println instructionText
  IO.println fieldOverview
  IO.println credits
  IO.println "\nPress ENTER to return to the main menu."
  _ ← (← IO.getStdin).getLine