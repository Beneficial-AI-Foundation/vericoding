-- <vc-preamble>
def ListNode.next : ListNode → Option ListNode
  | mk _ next => next

def ListNode.val : ListNode → Int
  | mk val _ => val

def removeZeroSumSublists : ListNode → Option ListNode := sorry
def listToArray : Option ListNode → List Int := sorry 

def arrayToList : List Int → Option ListNode := sorry

def sumList (l : List Int) : Int :=
  l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubsequence (sub post : List Int) : Bool :=
  match sub, post with
  | [], _ => true
  | _, [] => false
  | x::xs, y::ys => if x = y 
                    then isSubsequence xs ys
                    else isSubsequence (x::xs) ys
-- </vc-definitions>

-- <vc-theorems>
theorem no_zero_sum_sublists_after_removal (l : List Int) :
  let result := listToArray (removeZeroSumSublists (arrayToList l).get!)
  ∀ i j, i ≤ j → j < result.length →
    sumList ((result.take (j + 1)).drop i) ≠ 0 := sorry

theorem result_is_subsequence (l : List Int) :
  let result := listToArray (removeZeroSumSublists (arrayToList l).get!)
  isSubsequence result l = true := sorry

theorem all_positive_unchanged (l : List Int) :
  (∀ x ∈ l, x > 0) →
  listToArray (removeZeroSumSublists (arrayToList l).get!) = l := sorry

inductive IsAcyclic : ListNode → Prop where
  | nil : (n : ListNode) → Option.isNone (n.next) → IsAcyclic n
  | cons : (n : ListNode) → Option.isSome (n.next) → 
          IsAcyclic (Option.get! n.next) → IsAcyclic n

theorem linked_list_valid (l : List Int) :
  l ≠ [] →
  let result := (removeZeroSumSublists (arrayToList l).get!)
  ∀ node, result = some node → IsAcyclic node := sorry
-- </vc-theorems>