The local transport authority is organizing an online picture contest.
Participants must take pictures of transport means in an original way, and then post the picture on Instagram using a specific ```hashtag```.

The local transport authority needs your help. They want you to take out the ```hashtag``` from the posted message. Your task is to implement the function

```python
def omit_hashtag(message, hashtag):
```

## Examples 

```
* ("Sunny day! #lta #vvv", "#lta") -> "Sunny day!  #vvv" (notice the double space)
* ("#lta #picture_contest", "#lta") -> " #picture_contest"
```

## Notes

* When multiple occurences of the hashtag are found, delete only the first one.

* In C, you should modify the ```message```, as the function returns a void type. In Python, you should return the answer.

* There can be erroneous messages where the hashtag isn't present. The message should in this case stay untouched.

* The hashtag only consists of alphanumeric characters.

def omit_hashtag (message : String) (hashtag : String) : String := sorry 

def String.count (s t : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
