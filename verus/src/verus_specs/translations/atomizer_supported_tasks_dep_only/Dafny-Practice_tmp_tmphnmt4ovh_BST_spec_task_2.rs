//ATOM_PLACEHOLDER_Tree//ATOM_PLACEHOLDER_Main

// SPEC 

pub fn PrintTreeNumbersInorder(t: Tree)
{
}


//ATOM_PLACEHOLDER_NumbersInTree

//ATOM_PLACEHOLDER_NumbersInSequence

//ATOM_PLACEHOLDER_BST

//ATOM_PLACEHOLDER_Inorder

//ATOM_PLACEHOLDER_Ascending

//ATOM_PLACEHOLDER_NoDuplicates

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/
//ATOM_PLACEHOLDER_BuildBST

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
//ATOM_PLACEHOLDER_InsertBST
{
	match t0 
	{
		Empty => t = Node(x, Empty, Empty),

		Node(i, left, right) => 
		{
			let mut tmp: Tree = Empty;
			if x < i
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp = InsertBST(left, x);
				t = Node(i, tmp, right);
				ghost let right_nums = Inorder(right);
				ghost let left_nums = Inorder(left);
				ghost let all_nums = Inorder(t0);
				// assert all_nums[..|left_nums|] == left_nums;
				ghost let new_all_nums = Inorder(t);
				ghost let new_left_nums = Inorder(tmp);
				// assert Ascending(new_left_nums+ [i] + right_nums);



				
				
				lemma_all_small(new_left_nums,i);
				

			}
			else
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp = InsertBST(right, x);
				t = Node(i, left, tmp);

				ghost let right_nums = Inorder(right);
				ghost let left_nums = Inorder(left);
				ghost let all_nums = Inorder(t0);
				// assert all_nums[..|left_nums|] == left_nums;
				ghost let new_all_nums = Inorder(t);
				ghost let new_right_nums = Inorder(tmp);
				// assert Ascending(left_nums+ [i] + right_nums);


				// assert forall j :: j in NumbersInSequence(all_nums[|left_nums|+1..]) ==> j > i;
				// assert forall j :: j in NumbersInSequence(all_nums[|left_nums|+1..])+{x} ==> j > i;
				
				
				lemma_all_big(new_right_nums,i);
				
				// assert Ascending(new_right_nums+[i]);

			}
		}
	}
}

//ATOM_PLACEHOLDER_LemmaBinarySearchSubtree

//ATOM_PLACEHOLDER_LemmaAscendingSubsequence

//ATOM_PLACEHOLDER_unknown_3181 
proof fn lemma_all_small(q: seq<int>, i: int)
    requires(forall|k| k in NumbersInSequence(q) ==> k < i)
    requires(forall|k| 0 <= k < q.len() ==> q[k] in NumbersInSequence(q))
    ensures(forall|j| 0 <= j < q.len() ==> q[j] < i)
{}

//ATOM_PLACEHOLDER_unknown_3407 
proof fn lemma_all_big(q: seq<int>, i: int)
    requires(forall|k| k in NumbersInSequence(q) ==> k > i)
    requires(forall|k| 0 <= k < q.len() ==> q[k] in NumbersInSequence(q))
    ensures(forall|j| 0 <= j < q.len() ==> q[j] > i)
{}

proof fn lemma_all_big(q: seq<int>, i: int)
    requires(forall|k| k in NumbersInSequence(q) ==> k > i)
    requires(forall|k| 0 <= k < q.len() ==> q[k] in NumbersInSequence(q))
    ensures(forall|j| 0 <= j < q.len() ==> q[j] > i)
{}