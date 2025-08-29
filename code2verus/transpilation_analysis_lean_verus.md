# Lean to Verus Transpilation Analysis

## Summary
This document analyzes the correctness of the transpilation from Lean 4 to Verus by comparing examples from the Verina dataset with their corresponding transpilations in `artifacts/verina`.

## Examples Analyzed

### 1. findFirstOdd (Basic Example - verina_basic_49)

**Lean Specification:**
```lean
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0

def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  let indexed := a.toList.zipIdx
  let found := List.find? (fun (x, _) => isOdd x) indexed
  Option.map (fun (_, i) => i) found

@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)
```

**Verus Transpilation:**
```rust
// Helper function to check if a number is odd
spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// Precondition: array must be non-empty  
spec fn find_first_odd_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Postcondition specification that matches the Lean version exactly
spec fn find_first_odd_postcond(a: &Vec<i32>, result: Option<usize>) -> bool {
    match result {
        Some(idx) => {
            &&& idx < a.len()
            &&& is_odd(a[idx as int] as int)  
            &&& forall|j: int| 0 <= j < idx ==> !is_odd(a[j] as int)
        }
        None => forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int)
    }
}

// Implementation function that finds the first odd element
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    requires find_first_odd_precond(a)
    ensures find_first_odd_postcond(a, result)
{
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !is_odd(a[j] as int)
        decreases a.len() - i
    {
        if a[i] % 2 != 0 {
            return Some(i);
        }
        i += 1;
    }
    None
}
```

**Observations:**
- ✅ Helper functions correctly translated (isOdd → is_odd)
- ✅ Preconditions and postconditions accurately preserved
- ✅ Option type correctly mapped (Option Nat → Option<usize>)
- ✅ Array Int → Vec<i32> translation
- ⚠️ Implementation changed from functional (zipIdx, find?) to imperative (while loop)
- ✅ Postcondition logic preserved exactly
- ✅ Added loop invariants for verification

### 2. runLengthEncoder (Advanced Example - verina_advanced_68)

**Lean Specification:**
```lean
@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  True

def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  let chars : String → List Char := fun s => s.data
  let charEq : Char → Char → Bool := fun c1 c2 => c1 == c2
  let numToString : Nat → String := fun n =>
    let rec digits : Nat → List Char := fun n =>
      if n < 10 then
        [Char.ofNat (n + 48)]  -- ASCII '0' is 48
      else
        digits (n / 10) ++ [Char.ofNat (n % 10 + 48)]
    String.mk (digits n)
  
  let rec encode : List Char → Option Char → Nat → String :=
    fun input currentChar count =>
      match input with
      | [] =>
        match currentChar with
        | none => ""
        | some c => String.mk [c] ++ numToString count
      | c::rest =>
        match currentChar with
        | none => encode rest c 1
        | some c' =>
          if charEq c c' then
            encode rest c' (count + 1)
          else
            let currentPart := String.mk [c'] ++ numToString count
            currentPart ++ encode rest c 1
```

**Verus Transpilation:**
```rust
// Precondition for runLengthEncoder - always true as in the original
spec fn run_length_encoder_precond(input: Seq<char>) -> bool {
    true
}

// Helper function to check if character is digit
spec fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
}

// Simple run length encoder implementation
fn run_length_encoder(input: Vec<char>) -> (result: Vec<char>)
    requires run_length_encoder_precond(input@)
{
    if input.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut current_char = input[0];
    let mut count: u32 = 1;
    let mut i = 1;
    
    while i < input.len()
        invariant
            0 < input.len(),
            1 <= i <= input.len(),
            count >= 1,
            count <= i,
            result.len() >= 0,
        decreases input.len() - i
    {
        if input[i] == current_char {
            if count < u32::MAX {
                count += 1;
            }
        } else {
            // Add current character to result
            result.push(current_char);
            
            // Add count as digit characters
            let mut temp_count = count;
            let mut digits = Vec::new();
            
            while temp_count > 0
                invariant temp_count >= 0, digits.len() >= 0
                decreases temp_count
            {
                let digit_val = temp_count % 10;
                let digit_char = (('0' as u8) + (digit_val as u8)) as char;
                digits.push(digit_char);
                temp_count = temp_count / 10;
            }
            
            // Reverse digits to get correct order
            let mut j = digits.len();
            while j > 0
                invariant j <= digits.len()
                decreases j
            {
                j = j - 1;
                result.push(digits[j]);
            }
            
            current_char = input[i];
            count = 1;
        }
        i += 1;
    }
    // ...continues
}
```

**Observations:**
- ✅ Precondition correctly translated (always true)
- ⚠️ String → Vec<char> (lost String abstraction)
- ⚠️ Recursive functional implementation → imperative loops
- ✅ ASCII character handling preserved
- ⚠️ Added overflow checking for u32::MAX
- ✅ Core algorithm logic maintained
- ⚠️ Complex postcondition from Lean not fully translated

### 3. longestIncreasingSubsequence (Failed Advanced Example - verina_advanced_33)

**Lean Specification:**
```lean
@[reducible, simp]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  let max2 (a : Nat) (b : Nat) : Nat :=
    if a > b then a else b

  let rec helper (lst : List Int) (prev : Option Int) : Nat :=
    match lst with
    | [] => 0
    | h :: t =>
        let canTake : Bool :=
          if prev = none then true
          else if prev.get! < h then true else false
        let withTake : Nat :=
          if canTake then 1 + helper t (some h) else 0
        let withoutTake : Nat := helper t prev
        max2 withTake withoutTake

  let result := helper nums none
  result

@[reducible, simp]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
```

**Verus Transpilation:**
```rust
spec fn longest_increasing_subsequence_precond(nums: Seq<i32>) -> bool {
    true
}

fn max2(a: usize, b: usize) -> (result: usize)
    ensures result >= a && result >= b && (result == a || result == b)
{
    if a > b { a } else { b }
}

spec fn is_strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

spec fn all_subsequences(s: Seq<i32>) -> Set<Seq<i32>> {
    Set::new(|subseq: Seq<i32>| 
        exists|indices: Seq<int>| {
            &&& indices.len() == subseq.len()
            &&& (forall|i: int| 0 <= i < indices.len() ==> 0 <= #[trigger] indices[i] < s.len())  
            &&& (forall|i: int, j: int| 0 <= i < j < indices.len() ==> #[trigger] indices[i] < #[trigger] indices[j])
            &&& (forall|i: int| 0 <= i < indices.len() ==> subseq[i] == s[#[trigger] indices[i]])
        }
    )
}

fn helper(lst: Seq<i32>, prev: Option<i32>) -> (result: usize)
    decreases lst.len()
{
    assume(false); // Proof placeholder - would need actual implementation  
    0
}

spec fn longest_increasing_subsequence_postcond(nums: Seq<i32>, result: usize) -> bool {
    let all_subseq = all_subsequences(nums);
    let increasing_subseq_lens = Set::new(|len: int| 
        exists|subseq: Seq<i32>| all_subseq.contains(subseq) && is_strictly_increasing(subseq) && subseq.len() == len
    );
    increasing_subseq_lens.contains(result as int) &&
    (forall|len: int| increasing_subseq_lens.contains(len) ==> len <= result as int)
}
```

**Observations:**
- ✅ Precondition correctly translated
- ✅ Helper function max2 preserved with postcondition
- ⚠️ Main algorithm implementation incomplete (assume(false))
- ✅ Complex postcondition attempted but with different approach
- ⚠️ Lean's functional subsequence generation → Verus's set-theoretic spec
- ❌ Failed verification due to incomplete implementation
- ✅ Added trigger annotations for quantifier instantiation

## Key Findings

### Correct Translations:
1. **Basic Types**: Int → i32, Nat → usize, Bool → bool
2. **Option Types**: Option T → Option<T>
3. **Collections**: Array/List → Vec/Seq
4. **Preconditions/Postconditions**: Logical structure preserved
5. **Helper Functions**: Correctly translated with appropriate specs

### Notable Changes/Adaptations:
1. **Data Structures**:
   - `String` → `Vec<char>` or `Seq<char>`
   - `List Int` → `Seq<i32>` (for specs) or `Vec<i32>` (for exec)
   - `Array Int` → `Vec<i32>`

2. **Implementation Style**:
   - Functional recursive → Imperative loops
   - Pattern matching → if-else chains
   - List operations (zipIdx, find?) → manual iteration

3. **Verification Features**:
   - Added loop invariants
   - Added decreases clauses
   - Trigger annotations for quantifiers
   - Explicit overflow checking

4. **Specification Style**:
   - Lean's computational specs → Verus's logical specs
   - List comprehensions → Set comprehensions
   - Pairwise predicates → forall quantifiers

## Challenges in Transpilation:

1. **Complex Functional Constructs**: Lean's higher-order functions and list comprehensions are difficult to translate directly
2. **String Handling**: Loss of String abstraction when moving to Vec<char>
3. **Proof Obligations**: Some complex proofs couldn't be automatically translated (see assume(false))
4. **Postcondition Complexity**: Complex postconditions require manual reformulation

## Success Rate Analysis:

Based on the verina_results.yml file:
- The transpilation appears to have a high success rate for basic examples
- More complex examples (like verina_advanced_33) sometimes fail verification
- Failures often due to:
  - Incomplete implementations
  - Complex postcondition verification
  - Trigger selection issues in quantifiers

## Conclusion:

The Lean to Verus transpilation shows good preservation of logical meaning and program structure. The main challenges are:

1. **Implementation Gap**: Functional → imperative translation requires significant restructuring
2. **Specification Complexity**: Complex Lean specifications need manual adaptation
3. **Verification Challenges**: Some proofs don't translate automatically
4. **Type System Differences**: String handling and numeric types require adaptation

The transpiler makes reasonable choices but complex examples often need manual intervention for successful verification. The tool appears more successful with simpler, more straightforward specifications and implementations.
