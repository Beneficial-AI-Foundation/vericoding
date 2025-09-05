Your task is to determine the top 3 place finishes in a pole vault competition involving several different competitors. This is isn't always so simple, and it is often a source of confusion for people who don't know the actual rules.

Here's what you need to know:

As input, you will receive an array of objects. Each object contains the respective competitor's name (as a string) and his/her results at the various bar heights (as an array of strings):

[{name: "Sergey", results: ["", "O", "XO", "O", "XXO", "XXX", "", ""]}{name: "Jan", results: ["", "", "", "O", "O", "XO", "XXO", "XXX"]}{name: "Bruce", results: ["", "XO", "XXO", "XXX", "", "", "", ""]}{name: "HerrWert", results: ["XXX", "", "", "", "", "", "", ""]}]

In the array of strings described above, each string represents the vaulter's performance at a given height. The possible values are based on commonly used written notations on a pole vault scoresheet:
An empty string indicates that the vaulter did not jump at this height for a variety of possible reasons ("passed" at this height, was temporarily called away to a different track and field event, was already eliminated from competition, or withdrew due to injury, for example).An upper-case X in the string represents an unsuccessful attempt at the height. (As you may know, the vaulter is eliminated from the competition after three consecutive failed attempts.)An upper-case O represents a successful attempt. If present at all, this will be the final character in the string, because it indicates that the vaulter has now successfully completed this height and is ready to move on.

All vaulters will have a result string (though possibly empty) for every height involved in the competition, making it possible to match up the results of different vaulters with less confusion.

Obviously, your first task is to determine who cleared the greatest height successfully. In other words, who has a "O" mark at a higher array element than any other competitor? You might want to work through the arrays from right to left to determine this. In the most straightforward case, you would first determine the winner, then second place, and finally third place by this simple logic.

But what if there's a tie for one of these finishing places? Proceed as follows (according to American high school rules, at least):
First trace backwards to find the greatest height that both vaulters cleared successfully. Then determine who had the fewest unsuccessful attempts at this height (i.e., the fewest X's in the string for this height). This person wins the tie-break.But what if they're still tied with one another?  Do NOT continue to trace backwards through the heights! Instead, compare their total numbers of unsuccessful attempts at all heights in the competition. The vaulter with the fewest total misses wins the tie-break.But what if they're still tied? It depends on the finishing place:If it's for second or third place, the tie stands (i.e., is not broken).But if it's for first place, there must be a jump-off (like overtime or penalty kicks in other sports) to break the tie and determine the winner. (This jump-off occurs - hypothetically - after your code runs and is thus not a part of this kata.)

Return a single object as your result. Each place-finish that is included in the results (including at least first place as property "1st" and possibly second and third places as properties "2nd" and "3rd") should have as its value the respective vaulter's name. In the event of a tie, the value of the property is the names of all tied vaulters, in alphabetical order, separated by commas, and followed by the notation "(jump-off)" if the tie is for first place or "(tie)" if it's for second or third place.

Here are some possible outcomes to show you what I mean:
{1st: "Jan", 2nd: "Sergey"; 3rd: "Bruce"} (These results correspond to the sample input data given above.){1st: "Julia", 2nd: "Madi, Emily (tie)}"{1st: "Caleb, Dustin (jump-off)", 3rd: "Sam"}{1st: "Meredith", 2nd: "Maddy", 3rd: "Cierra, Sara (tie)"}{1st: "Alex, Basti, Max (jump-off)"}

If you are familiar with the awarding of place finishes in sporting events or team standings in a league, then you know that there won't necessarily be a 2nd or 3rd place, because ties in higher places "bump"  all lower places downward accordingly.

One more thing: You really shouldn't change the array of objects that you receive as input. This represents the physical scoresheet. We need this "original document" to be intact, so that we can refer back to it to resolve a disputed result!

Have fun with this!

- - - - -

Notes for the Python version:

The rules for the Python version are the same as the original JavaScript version. 

The input and output will look the same as the JavaScript version. But, the JavaScript objects will be replaced by Python dictionaries. The JavaScript arrays will be replaced by Python lists. The Python function name was changed to include underscores as is customary with Python names. The example below should help clarify all of this.

The input for the Python version will be a list containing dictionaries with the competitors' names and results. The names in the dictionaries are strings. The results are lists with a list of strings. And example follows.

score_pole_vault([
        {"name": "Linda", "results": ["XXO", "O","XXO", "O"]},
        {"name": "Vickie", "results": ["O","X", "", ""]},
        {"name": "Debbie", "results": ["XXO", "O","XO", "XXX"]},
        {"name": "Michelle", "results": ["XO","XO","XXX",""]},
        {"name": "Carol", "results": ["XXX", "","",""]}
])

The returned results should be in a dictionary with one to three elements. 

Examples of possible returned results:

  {'1st': 'Linda', '2nd': 'Debbie', '3rd': 'Michelle'}

  {'1st': 'Green, Hayes (jump-off)', '3rd': 'Garcia'}           
  Note: Since first place was tied in this case, there is no 2nd place awarded.

  {'1st': 'Wilson', '2nd': 'Laurie', '3rd': 'Joyce, Moore (tie)'}

I have tried to create test cases that have every concievable tie situation.

Have fun with this version, as well!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
