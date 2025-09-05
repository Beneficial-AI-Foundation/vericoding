A great flood has hit the land, and just as in Biblical times we need to get the animals to the ark in pairs. We are only interested in getting one pair of each animal, and not interested in any animals where there are less than 2....they need to mate to repopulate the planet after all!

You will be given a list of animals, which you need to check to see which animals there are at least two of, and then return a dictionary containing the name of the animal along with the fact that there are 2 of them to bring onto the ark.

---

```python
>>> two_by_two(['goat', 'goat', 'rabbit', 'rabbit', 'rabbit', 'duck', 'horse', 'horse', 'swan'])
{'goat': 2, 'horse': 2, 'rabbit': 2}

# If the list of animals is empty, return False as there are no animals to bring onto the ark and we are all doomed!!!
>>> two_by_two([])
False

# If there are no pairs of animals, return an empty dictionary
>>> two_by_two(['goat'])
{}
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded