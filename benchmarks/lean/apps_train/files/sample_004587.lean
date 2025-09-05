### Background
One way to order a nested (reddit-style) commenting system is by giving each comment a rank. 

Generic comments on a thread start with rank 1 and increment, so the second comment on a thread would have rank 2. A reply to comment 1 will be ranked 1.1, and a reply to comment 1.1 will be ranked 1.1.1 . The second comment to reply to comment 1 would be ranked 1.2 .

Note that since 1.1.1 is a valid rank, the ranks given are of type string.   

### Task: 
Given a list of comment ranks (strings), order them as a comment thread would appear 

### Assumptions:  
* there will always be a rank 1 in the given input
* ranks are of type string
* rank numbers are incremented, and not skippped (1.1 could be followed by 1.2, not 1.3)

### Example order:
```
[
  '1',
  '1.1',
  '1.2',
  '1.2.1',
  '2',
  '3',
  '3.1',
  '3.1.1',
  '3.2'
]
```

def sort_ranks (ranks: List String) : List String := sorry

def is_valid_version (s: String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
