Your task is to ___Reverse and Combine Words___. It's not too difficult, but there are some things you have to consider...

### So what to do?

Input: String containing different "words" separated by spaces

```
1. More than one word? Reverse each word and combine first with second, third with fourth and so on...
   (odd number of words => last one stays alone, but has to be reversed too)
2. Start it again until there's only one word without spaces
3. Return your result...
```

### Some easy examples:
```
Input:  "abc def"
Output: "cbafed"

Input:  "abc def ghi 123"
Output: "defabc123ghi"

Input:  "abc def gh34 434ff 55_eri 123 343"
Output: "43hgff434cbafed343ire_55321"
```

I think it's clear?! First there are some static tests, later on random tests too...

### Hope you have fun! :-)

def reverseAndCombineText (text : String) : String := sorry 

-- Result length should match total chars across merged words

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
