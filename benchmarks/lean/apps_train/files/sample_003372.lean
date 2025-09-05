Base on the fairy tale [Diamonds and Toads](https://en.wikipedia.org/wiki/Diamonds_and_Toads) from Charles Perrault. In this kata you will have to complete a function that take 2 arguments: 

- A string, that correspond to what the daugther says.
- A string, that tell you wich fairy the girl have met, this one can be `good` or `evil`. 

The function should return the following count as a hash:

- If the girl have met the `good` fairy:
  - count 1 `ruby` everytime you see a `r` and 2 everytime you see a `R`
  - count 1 `crystal` everytime you see a `c` and 2 everytime you see a `C`
- If the girl have met the `evil` fairy: 
  - count 1 `python` everytime you see a `p` and 2 everytime uou see a `P`
  - count 1 `squirrel` everytime you see a `s` and 2 everytime you see a `S`

**Note**: For this kata I decided to remplace the normal `Diamonds` and `Toads` by some programming languages. And just discover that [Squirrel](https://en.wikipedia.org/wiki/Squirrel_(programming_language) is a programming language.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded