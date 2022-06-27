# lean-snakebird

*lean-snakebird* is a Lean-based implementation of the game [Snakebird](https://store.steampowered.com/app/357300/Snakebird/). This project was inspired by [lean4-maze](https://github.com/dwrensha/lean4-maze) which shows off the meta-programming capabilities of Lean 4. Accordingly, *lean-snakebird* implements a [DSL](Snakebird/Levels/Syntax.lean) in Lean 4 which can be used to define levels of the game:

```lean
def level8 :=
••••••••••••••◎•
••••••••••••••••
••┏━1••••••••▦▦▦
•╺┛0━╸•••••✸✸✸▦▦
▦▦▦▦▦▦✸✸✸••✸••••
•▦▦▦▦▦••✸✸▦✸••••
••••••••••••••••
••••••••••••••••
∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼
```

To run the game:

1. Clone this repository.
2. Run `lake build`.
3. Run `./build/bin/snakebird`.