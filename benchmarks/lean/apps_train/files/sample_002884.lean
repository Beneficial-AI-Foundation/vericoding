Task
=======

Make a custom esolang interpreter for the language Tick. Tick is a descendant of [Ticker](https://www.codewars.com/kata/esolang-ticker) but also very different data and command-wise.

Syntax/Info
========

Commands are given in character format. Non-command characters should be ignored. Tick has an potentially infinite memory as opposed to Ticker(which you have a special command to add a new cell) and only has 4 commands(as opposed to 7). Read about this esolang [here](https://esolangs.org/wiki/Tick).

Commands
========

`>`: Move data selector right

`<`: Move data selector left(infinite in both directions)

`+`: Increment memory cell by 1. 255+1=0

`*`: Add ascii value of memory cell to the output tape.

Examples
========

**Hello world!**

```
'++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++**>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*<<*>>>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*<<<<*>>>>>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++*'
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
