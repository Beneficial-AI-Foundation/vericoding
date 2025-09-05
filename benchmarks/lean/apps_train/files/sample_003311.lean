Your task is to determine how many files of the copy queue you will be able to save into your Hard Disk Drive. The files must be saved in the order they appear in the queue. 

### Input:

* Array of file sizes `(0 <= s <= 100)`
* Capacity of the HD `(0 <= c <= 500)`

### Output:

* Number of files that can be fully saved in the HD. 

### Examples:

```
save([4,4,4,3,3], 12) -> 3
# 4+4+4 <= 12, but 4+4+4+3 > 12
```

```
save([4,4,4,3,3], 11) -> 2
# 4+4 <= 11, but 4+4+4 > 11
```

Do not expect any negative or invalid inputs.

def sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible