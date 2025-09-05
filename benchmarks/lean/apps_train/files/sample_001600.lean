# RoboScript #3 - Implement the RS2 Specification

## Disclaimer

The story presented in this Kata Series is purely fictional; any resemblance to actual programming languages, products, organisations or people should be treated as purely coincidental.

## About this Kata Series

This Kata Series is based on a fictional story about a computer scientist and engineer who owns a firm that sells a toy robot called MyRobot which can interpret its own (esoteric) programming language called RoboScript.  Naturally, this Kata Series deals with the software side of things (I'm afraid Codewars cannot test your ability to build a physical robot!).

## Story

Last time, you implemented the RS1 specification which allowed your customers to write more concise scripts for their robots by allowing them to simplify consecutive repeated commands by postfixing a non-negative integer onto the selected command.  For example, if your customers wanted to make their robot move 20 steps to the right, instead of typing `FFFFFFFFFFFFFFFFFFFF`, they could simply type `F20` which made their scripts more concise.  However, you later realised that this simplification wasn't enough.  What if a set of commands/moves were to be repeated?  The code would still appear cumbersome.  Take the program that makes the robot move in a snake-like manner, for example.  The shortened code for it was `F4LF4RF4RF4LF4LF4RF4RF4LF4LF4RF4RF4` which still contained a lot of repeated commands.

## Task

Your task is to allow your customers to further shorten their scripts and make them even more concise by implementing the newest specification of RoboScript (at the time of writing) that is RS2.  RS2 syntax is a superset of RS1 syntax which means that all valid RS1 code from the previous Kata of this Series should still work with your RS2 interpreter.  The only main addition in RS2 is that the customer should be able to group certain sets of commands using round brackets.  For example, the last example used in the previous Kata in this Series:

LF5RF3RF3RF7

... can be expressed in RS2 as:

LF5(RF3)(RF3R)F7

Or ... 

(L(F5(RF3))(((R(F3R)F7))))

Simply put, your interpreter should be able to deal with nested brackets of any level.

And of course, brackets are useless if you cannot use them to repeat a sequence of movements!  Similar to how individual commands can be postfixed by a non-negative integer to specify how many times to repeat that command, a sequence of commands grouped by round brackets `()` should also be repeated `n` times provided a non-negative integer is postfixed onto the brackets, like such:

(SEQUENCE_OF_COMMANDS)n

... is equivalent to ... 

SEQUENCE_OF_COMMANDS...SEQUENCE_OF_COMMANDS (repeatedly executed "n" times)

For example, this RS1 program:

F4LF4RF4RF4LF4LF4RF4RF4LF4LF4RF4RF4

... can be rewritten in RS2 as:

F4L(F4RF4RF4LF4L)2F4RF4RF4

Or:

F4L((F4R)2(F4L)2)2(F4R)2F4

All 4 example tests have been included for you.  Good luck :D

## Kata in this Series

1. [RoboScript #1 - Implement Syntax Highlighting](https://www.codewars.com/kata/roboscript-number-1-implement-syntax-highlighting)
2. [RoboScript #2 - Implement the RS1 Specification](https://www.codewars.com/kata/roboscript-number-2-implement-the-rs1-specification)
3. **RoboScript #3 - Implement the RS2 Specification**
4. [RoboScript #4 - RS3 Patterns to the Rescue](https://www.codewars.com/kata/594b898169c1d644f900002e)
5. [RoboScript #5 - The Final Obstacle (Implement RSU)](https://www.codewars.com/kata/5a12755832b8b956a9000133)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible