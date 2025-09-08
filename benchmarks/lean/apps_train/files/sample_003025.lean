/-
Task
======

Make a custom esolang interpreter for the language [InfiniTick](https://esolangs.org/wiki/InfiniTick). InfiniTick is a descendant of [Tick](https://esolangs.org/wiki/tick) but also very different. Unlike Tick, InfiniTick has 8 commands instead of 4. It also runs infinitely, stopping the program only when an error occurs. You may choose to do the [Tick](https://www.codewars.com/kata/esolang-tick) kata first.

Syntax/Info
======

InfiniTick runs in an infinite loop. This makes it both harder and easier to program in. It has an infinite memory of bytes and an infinite output amount. The program only stops when an error is reached. The program is also supposed to ignore non-commands.

Commands
======

`>`: Move data selector right.

`<`: Move data selector left.

`+`: Increment amount of memory cell. Truncate overflow: 255+1=0.

`-`: Decrement amount of memory cell. Truncate overflow: 0-1=255.

`*`: Add ascii value of memory cell to the output tape.

`&`: Raise an error, ie stop the program.

`/`: Skip next command if cell value is zero.

`\`: Skip next command if cell value is nonzero.

Examples
======

**Hello world!**

The following is a valid hello world program in InfiniTick.

```
'++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++**>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*<<*>>>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*<<<<*>>>>>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*>+++++++++++++++++++++++++++++++++*&'
```

Notes
======

* Please be wordy and post your likes/dislikes in the discourse area.
* If this kata is a duplicate or uses incorrect style, this is not an issue, this is a suggestion.
* Please don't edit this kata just to change the estimated rank. Thank you!
-/

-- <vc-helpers>
-- </vc-helpers>

def interpreter (s : String) : String :=
  sorry

theorem output_valid_chars {tape : String} 
  (h : String.contains tape '&') :
  ∀ c, c ∈ (interpreter tape).data → 0 ≤ Char.toNat c ∧ Char.toNat c < 256 :=
sorry

theorem arithmetic_wrapping (n : Nat) :
  let tape := String.mk ((List.replicate n '+') ++ 
               (List.replicate n '-') ++ ['*', '&'])
  interpreter tape = "\u0000" :=
sorry

/-
info: '\x00'
-/
-- #guard_msgs in
-- #eval interpreter "\\h*&"

/-
info: '\x00'
-/
-- #guard_msgs in
-- #eval interpreter "+-*&"

/-
info: '\x01'
-/
-- #guard_msgs in
-- #eval interpreter "+*&"

-- Apps difficulty: introductory
-- Assurance level: unguarded