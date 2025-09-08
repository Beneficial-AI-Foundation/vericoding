/-
Chef Loves to listen to remix songs, but currently he had already finished the entire playlist of remix songs.
As Chef is smart, so he thought let's make my own remix songs of the original songs.
Chef is not having much knowledge of making remix songs, so he came up with the simple technique in which he will pick the word which contains the smallest number of characters from the lyrics of the song, and then he will append that word to the start and end of the lyrics, also Chef will insert this word between every two words of the lyrics.
Note: While inserting a new word Chef will also insert extra white-spaces, so that every word in the final remixed lyrics is separated by space.
It is Recommended to use fast Input/Ouput techniques.

-----Input:-----
- The input contains the text $S$, which denotes the lyrics of the song.

-----Output:-----
- Print the Remixed, lyrics as done by Chef.

-----Constraints:-----
- $1 \leq Length of text $S$ \leq 10^7$

-----Sample Input:-----
Mai Hu Jiyaan

-----Sample Output:-----
Hu Mai Hu Hu Hu Jiyaan Hu
-/

-- <vc-helpers>
-- </vc-helpers>

def processText (text : String) : String :=
  sorry

theorem process_text_starts_ends_with_i (text : List String) (h : text.length > 0) : 
  let result := processText (String.intercalate " " text)
  result.take 1 = "I" ∧ result.takeRight 1 = "I" :=
  sorry

theorem process_text_i_count (text : List String) (h : text.length > 0) : 
  let result := processText (String.intercalate " " text)
  let iCount := String.length result - String.length (String.replace result "I" "")
  iCount = text.length + 1 :=
  sorry

theorem process_text_alternating_i (text : List String) (h : text.length > 0) :
  let result := processText (String.intercalate " " text)
  let words := String.split result (· = ' ')
  ∀ i, i < words.length → i % 2 = 0 → words[i]! = "I" :=
  sorry

theorem process_text_preserves_words (text : String) (h : text.length > 0) :
  let result := processText text
  let inputWords := String.split text (· = ' ') |>.filter (· ≠ "")
  let outputWords := String.split result (· = ' ') |>.filter (· ≠ "I")
  inputWords = outputWords :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded