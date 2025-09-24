-- <vc-preamble>
def defaultTweetMap : TweetMap := fun _ => []

instance : Inhabited TweetCounts where
  default := ⟨defaultTweetMap⟩

def List.sorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

def List.isPermOf (l₁ l₂ : List Int) : Prop :=
  l₁.length = l₂.length ∧ ∀ x, (l₁.filter (· = x)).length = (l₂.filter (· = x)).length

/- Records a tweet -/

def TweetCounts.recordTweet (tc : TweetCounts) (name : String) (time : Int) : TweetCounts :=
sorry

/- Gets tweet counts per frequency -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TweetCounts.getTweetCountsPerFrequency (tc : TweetCounts) (freq : String) (name : String) (startTime : Int) (endTime : Int) : List Int :=
sorry

/- Counting tweets in a time window returns non-empty list with non-negative counts that sum to number of tweets in window -/
-- </vc-definitions>

-- <vc-theorems>
theorem tweet_count_properties (times : List Int) (name : String) (freq : String) (delta : Int)
    (h1 : times.length > 0)
    (h2 : delta > 0)
    (h3 : delta ≤ 1000)
    (h4 : ∀ t ∈ times, t ≥ 0 ∧ t ≤ 100000) :
    let tc : TweetCounts := default
    let tc' := times.foldl (fun acc t => TweetCounts.recordTweet acc name t) tc
    let minTime := times.minimum?.get!
    let result := tc'.getTweetCountsPerFrequency freq name minTime (minTime + delta)
    result.length > 0 ∧
    (∀ count ∈ result, count ≥ 0) ∧
    result.length = (times.filter (fun t => minTime ≤ t ∧ t ≤ minTime + delta)).length :=
sorry

/- Recording a single tweet should store exactly that tweet -/

theorem single_tweet_record (time : Int) (name : String)
    (h1 : time ≥ 0)
    (h2 : time ≤ 100000) :
    let tc : TweetCounts := default
    let tc' := TweetCounts.recordTweet tc name time
    tc'.tweets name = [time] :=
sorry

/- Tweet times should be stored in sorted order -/

theorem sorted_tweets (times : List Int) (name : String)
    (h1 : times.length ≥ 2)
    (h2 : times.length ≤ 100)
    (h3 : ∀ t ∈ times, t ≥ 0 ∧ t ≤ 100000) :
    let tc : TweetCounts := default
    let tc' := times.foldl (fun acc t => TweetCounts.recordTweet acc name t) tc
    (tc'.tweets name).sorted ∧ 
    (tc'.tweets name).isPermOf times :=
sorry

/- Getting counts for unknown tweet name should throw error -/

theorem unknown_tweet_name_error (name : String) :
    let tc : TweetCounts := default
    ¬(∃ result, tc.getTweetCountsPerFrequency "minute" name 0 10 = result) :=
sorry
-- </vc-theorems>