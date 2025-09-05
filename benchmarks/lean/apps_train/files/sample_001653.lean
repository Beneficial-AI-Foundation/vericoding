Kate constantly finds herself in some kind of a maze. Help her to find a way out!.

For a given maze and Kate's position find if there is a way out. Your function should return True or False.

Each maze is defined as a list of strings, where each char stays for a single maze "cell". ' ' (space) can be stepped on, '#' means wall and 'k' stays for Kate's starting position. Note that the maze may not always be square or even rectangular.

Kate can move left, up, right or down only.

There should be only one Kate in a maze. In any other case you have to throw an exception.

Example input
=============
```
['# ##',
 '# k#',
 '####']
```

Example output
==============
True

Example input
=============
```
['####'.
 '# k#',
 '####']
```

Example output
==============
False

def isValidMaze (maze : List String) : Bool := sorry
def hasExit (maze : List String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded