###Story
Sometimes we are faced with problems when we have a big nested dictionary with which it's hard to work. Now, we need to solve this problem by writing a function that will flatten a given dictionary.

###Info
Python dictionaries are a convenient data type to store and process configurations. They allow you to store data by keys to create nested structures. You are given a dictionary where the keys are strings and the values are strings or dictionaries. The goal is flatten the dictionary, but save the structures in the keys. The result should be a dictionary without the nested dictionaries. The keys should contain paths that contain the parent keys from the original dictionary. The keys in the path are separated by a `/`. If a value is an empty dictionary, then it should be replaced by an empty string `""`.

###Examples
```python
{
    "name": {
        "first": "One",
        "last": "Drone"
    },
    "job": "scout",
    "recent": {},
    "additional": {
        "place": {
            "zone": "1",
            "cell": "2"
        }
    }
}
```
The result will be:
```python
{"name/first": "One",           #one parent
 "name/last": "Drone",
 "job": "scout",                #root key
 "recent": "",                  #empty dict
 "additional/place/zone": "1",  #third level
 "additional/place/cell": "2"}
```

***`Input: An original dictionary as a dict.`***
***`Output: The flattened dictionary as a dict.`***
***`Precondition:
Keys in a dictionary are non-empty strings.
Values in a dictionary are strings or dicts.
root_dictionary != {}`***

```python
flatten({"key": "value"}) == {"key": "value"}
flatten({"key": {"deeper": {"more": {"enough": "value"}}}}) == {"key/deeper/more/enough": "value"}
flatten({"empty": {}}) == {"empty": ""}
```

def flatten {α : Type} [ToString α] (d : Dict α (Dict α String)) : Dict α String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
