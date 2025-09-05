You're fed up about changing the version of your software manually. Instead, you will create a little script that will make it for you.

# Exercice

Create a function `nextVersion`, that will take a string in parameter, and will return a string containing the next version number.

For example:

# Rules

All numbers, except the first one, must be lower than 10: if there are, you have to set them to 0 and increment the next number in sequence.

You can assume all tests inputs to be valid.

def splitVersion (v : String) : Version := sorry
def joinVersion (v : Version) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded