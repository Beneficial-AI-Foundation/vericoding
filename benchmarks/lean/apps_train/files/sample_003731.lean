# Letterss of Natac
In a game I just made up that doesn’t have anything to do with any other game that you may or may not have played, you collect resources on each turn and then use those resources to build settlements, roads, and cities or buy a development. Other kata about this game can be found [here](https://www.codewars.com/collections/59e6938afc3c49005900011f).

## Task
This kata asks you to implement the function `build_or_buy(hand)` , which takes as input a `hand`, the resources you have (a string of letters representing the resources you have), and returns a list of the unique game objects you can build or buy given your hand. 

There are five different resources, `'b'`, `'w'`, `'g'`, `'s'`, and `'o'`.

Game objects and the resources required to build or buy them are as follows:
1. `'road'`: `bw`
2. `'settlement'`: `bwsg`
3. `'city'`: `ooogg`
4. `'development'`: `osg`

## Examples
```python
build_or_buy("bwoo")  => ['road']
build_or_buy("bwsg")  => ['road', 'settlement'] or ['settlement', 'road']
build_or_buy("")      => []
build_or_buy("ogogoogogo")  => ['city']

```

## Notes: 
1. Don't mutate the hand
2. The order of the returned list doesn't matter
3. You do not have to test for whether a hand is valid. 
4. The list will be interpreted to mean 'you can build any of these objects,' not 'you can build all these objects in one play'. See example 2 above, even though there is only one `'b'` and one `'w'` in `hand`, both `Road()` and `Settlement()` are in the list. 
5. A hand can be empty. In the event a hand is empty, you can't build or buy anything, so return an empty list, see example 3 above.
6. Hand are between 0 and 39 in length.

def build_or_buy (hand : String) : List String := sorry

def ValidResources := "bwsog"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
