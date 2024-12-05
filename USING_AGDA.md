# Using Agda

mvrnote: under construction

## Using `agda-mode`

Test your installation by navigating to the first homework file
(`lectures/1--Type-Theory/1-1--Types-and-Functions.lagda.md`), and
loading it into Agda as follows.

Regardless of whether you are using Emacs or VSCode, most Agda
keybindings involve holding down Control or Meta (a.k.a. Alt) and
pressing other keys. Loading and checking an Agda file has the
keybinding `C-c C-l`, so to load the current file into Agda, hold down
Control then press `c` followed by `l`, you do not have to let go of
Control in between.

Here are some of the more useful keys, most of which will be explained
as we work through the exercises:

* `C-c C-l`: Load and check the file
* `M-.`: Jump to the definition of whatever your cursor is on
* `C-c C-f`: Move to next goal (forward)
* `C-c C-b`: Move to previous goal (backwards)

* `C-c C-c`: Case split (specify an argument to split on)
* `C-c C-r`: Refine goal (Add a `λ` if the goal is a function, add a
  `,` if the goal is a pair, etc. Not always the right move!)
* `C-c C-.`: Show the goal type, context and inferred type

If you are using Emacs, then most of the keybindings used in the
editor for ordinary editing and navigation are also of that form. For
example:

* `C-x C-f`: Open a file
* `C-x C-s`: Save the current file
* `C-x C-b`: See all the things ("buffers") you have open
* `C-x b`: Choose a buffer to switch to
* `C-_`: Undo
* `M-_`: Redo

## Agda Tricks:

* mvrnote: `C-c C-=` and `C-c C-s` for solving goals that are known to Agda

## Troubleshooting Agda

mvrnote: collect common issues

* mvrnote: Variable not in scope because you undo filling a hole
* _I can't input Unicode characters in Emacs by typing `\`!_ You may have accidentally disabled the input mode by pressing `C-\`, type `C-\` again to turn it back on.
* Termination checker fails
* Agda is busy with something, `C-c C-x C-r` to restart it
