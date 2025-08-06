use vstd::prelude::*;

verus!{

	fn main() {
	}

	fn myVecClone(v: &Vec<i32>) -> (result: Vec<i32>) 
		requires v.len() <= usize::MAX
		ensures result@ == v@
	{
		let mut result = Vec::new();
		let mut i = 0;
		/* code modified by LLM (iteration 2): added decreases clause and loop invariant */
		while i < v.len()
			invariant 
				i <= v.len(),
				result.len() == i,
				forall|j: int| 0 <= j < i ==> result@[j] == v@[j]
			decreases v.len() - i
		{
			result.push(v[i]);
			i += 1;
		}
		result
	}

	pub fn generate_all_combinations(n: i32, k: i32) -> Vec<Vec<i32>> 
	{
		let mut total_list = Vec::new();
		let mut current_list = Vec::new();
		
		if k > 0 && n > 0 && k <= n {
			create_all_state(1, n, k, &mut current_list, &mut total_list);
		}
		
		total_list
	}

	fn create_all_state
	(
		increment: i32,
		total_number: i32,
		level: i32,
		current_list: &mut Vec<i32>,
		total_list: &mut Vec<Vec<i32>>,
	) 
		requires 
			increment >= 1,
			total_number >= 1,
			level >= 0
		decreases level, (total_number - increment + 1) as nat
	{
		if level == 0 {
			let cloned = myVecClone(current_list);
			total_list.push(cloned);
			return;
		}
		
		if increment > total_number {
			return;
		}
		
		let mut i = increment;
		/* code modified by LLM (iteration 2): added decreases clause and loop invariant */
		while i <= total_number - level + 1
			invariant 
				i >= increment,
				increment >= 1,
				total_number >= 1,
				level > 0
			decreases (total_number - level + 1) - i + 1
		{
			current_list.push(i);
			create_all_state(i + 1, total_number, level - 1, current_list, total_list);
			current_list.pop();
			i += 1;
		}
	}
}