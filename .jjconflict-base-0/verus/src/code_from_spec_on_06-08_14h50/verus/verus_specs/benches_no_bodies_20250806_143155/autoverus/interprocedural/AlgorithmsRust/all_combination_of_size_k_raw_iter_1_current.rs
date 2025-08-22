use vstd::prelude::*;

verus!{

	fn main() {
	}

	fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
		let mut result = Vec::new();
		let mut i = 0;
		while i < v.len() {
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
		while i <= total_number - level + 1 {
			current_list.push(i);
			create_all_state(i + 1, total_number, level - 1, current_list, total_list);
			current_list.pop();
			i += 1;
		}
	}
}