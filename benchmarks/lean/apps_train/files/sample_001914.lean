Given the head of a linked list, we repeatedly delete consecutive sequences of nodes that sum to 0 until there are no such sequences.
After doing so, return the head of the final linked list.  You may return any such answer.

(Note that in the examples below, all sequences are serializations of ListNode objects.)
Example 1:
Input: head = [1,2,-3,3,1]
Output: [3,1]
Note: The answer [1,2,1] would also be accepted.

Example 2:
Input: head = [1,2,3,-3,4]
Output: [1,2,4]

Example 3:
Input: head = [1,2,3,-3,-2]
Output: [1]

Constraints:

The given linked list will contain between 1 and 1000 nodes.
Each node in the linked list has -1000 <= node.val <= 1000.

def ListNode.next : ListNode → Option ListNode
  | mk _ next => next

def ListNode.val : ListNode → Int
  | mk val _ => val

def removeZeroSumSublists : ListNode → Option ListNode := sorry
def listToArray : Option ListNode → List Int := sorry 

def arrayToList : List Int → Option ListNode := sorry

def sumList (l : List Int) : Int :=
  l.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
