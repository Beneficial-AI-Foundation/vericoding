A group of friends (n >= 2) have reunited for a get-together after 
a very long time. 

They agree that they will make presentations on holiday destinations 
or expeditions they have been to only if it satisfies **one simple rule**: 
> the holiday/journey being presented must have been visited _only_ by the presenter and no one else from the audience.

Write a program to output the presentation agenda, including the
presenter and their respective presentation titles. 

---
### EXAMPLES

```python
presentation_agenda([
    {'person': 'Abe', 'dest': ['London', 'Dubai']},
    {'person': 'Bond', 'dest': ['Melbourne', 'Dubai']}
]) == [{'person': 'Abe', 'dest': ['London']},
       {'person': 'Bond', 'dest': ['Melbourne']}]

presentation_agenda([
    {'person': 'Abe', 'dest': ['Dubai']},
    {'person': 'Brad', 'dest': ['Dubai']}
]) == []

presentation_agenda([
    {'person': 'Abe', 'dest': ['London', 'Dubai']},
    {'person': 'Bond', 'dest': ['Melbourne', 'Dubai']},
    {'person': 'Carrie', 'dest': ['Melbourne']},
    {'person': 'Damu', 'dest': ['Melbourne', 'Dubai', 'Paris']}
]) == [{'person': 'Abe',  'dest': ['London']},
       {'person': 'Damu', 'dest': ['Paris']}]

```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded