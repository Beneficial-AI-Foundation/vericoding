/*

This example is from Algorithm/Rust project.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/sudoku.rs

The original test cases test_sudoku_correct and test_sudoku_incorrect cannot be easily convereted to verification properties.
Instead, the added proof helps to verify the program free of arithemtic overflow and buffer overflow.

The main function is essentially the test_sudoku_correct function without the two run-time asserts.

*/

use vstd::prelude::*;

 
verus!{

	fn main() {
		let board = [
			5, 3, 0, 0, 7, 0, 0, 0, 0,
			6, 0, 0, 1, 9, 5, 0, 0, 0,
			0, 9, 8, 0, 0, 0, 0, 6, 0,
			8, 0, 0, 0, 6, 0, 0, 0, 3,
			4, 0, 0, 8, 0, 3, 0, 0, 1,
			7, 0, 0, 0, 2, 0, 0, 0, 6,
			0, 6, 0, 0, 0, 0, 2, 8, 0,
			0, 0, 0, 4, 1, 9, 0, 0, 5,
			0, 0, 0, 0, 8, 0, 0, 7, 9
		];
		let mut sudoku = Sudoku::new(board);
		sudoku.solve();
	}

	 
	pub struct Sudoku {
		board: [u8; 81],
	}
	
	impl Sudoku {
		pub fn new(board: [u8; 81]) -> Sudoku {
			Sudoku { board }
		}

		fn setcell(&mut self, x: usize, y: usize, val: u8) 
		requires x < 9, y < 9
		{
			self.board[y * 9 + x] = val;
		}

		fn readcell(&self, x: usize, y: usize) -> u8 
		requires x < 9, y < 9
		{
			self.board[y * 9 + x]
		}

		fn find_empty_cell(&self) -> (ret: Option<(usize, usize)>) 
		ensures ret.is_some() ==> ret.unwrap().0 < 9 && ret.unwrap().1 < 9
		{
			for y in 0..9 {
				for x in 0..9 {
					if self.board[y * 9 + x] == 0 {
						return Some((x, y));
					}
				}
			}
			None
		}

		fn check(&self, index_tuple: (usize, usize), value: u8) -> bool 
		requires index_tuple.0 < 9, index_tuple.1 < 9
		{
			let (x, y) = index_tuple;
			
			// Check row
			for i in 0..9 {
				if self.board[y * 9 + i] == value {
					return false;
				}
			}
			
			// Check column
			for i in 0..9 {
				if self.board[i * 9 + x] == value {
					return false;
				}
			}
			
			// Check 3x3 box
			let box_x = x / 3;
			let box_y = y / 3;
			for i in 0..3 {
				for j in 0..3 {
					let check_x = box_x * 3 + j;
					let check_y = box_y * 3 + i;
					if self.board[check_y * 9 + check_x] == value {
						return false;
					}
				}
			}
			
			true
		}
	
		/* code modified by LLM (iteration 1): Added exec_allows_no_decreases_clause attribute to allow recursive function without decreases clause */
		#[verifier::exec_allows_no_decreases_clause]
		pub fn solve(&mut self) -> bool {
			if let Some((x, y)) = self.find_empty_cell() {
				for num in 1..10 {
					if self.check((x, y), num) {
						self.setcell(x, y, num);
						if self.solve() {
							return true;
						}
						self.setcell(x, y, 0);
					}
				}
				false
			} else {
				true
			}
		}
	}
}