You're looking through different hex codes, and having trouble telling the difference between  #000001  and  #100000 

We need a way to tell which is red, and which is blue!

That's where you create ```hex_color()```!

It should read an RGB input, and return whichever value (red, blue, or green) is of greatest concentration!

But, if multiple colors are of equal concentration, you should return their mix!

```python
red + blue = magenta

green + red = yellow

blue + green = cyan

red + blue + green = white
```

One last thing, if the string given is empty, or has all 0's, return black!

Examples:
```python
hex_color('087 255 054') == 'green'
hex_color('181 181 170') == 'yellow'
hex_color('000 000 000') == 'black'
hex_color('001 001 001') == 'white'
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded