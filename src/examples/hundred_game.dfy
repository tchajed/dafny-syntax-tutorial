datatype State = State(num: nat, player1: bool)

datatype Step = Step(take: nat)

ghost predicate ValidMove(step: Step, s: State) {
  && 1 <= step.take <= 10
  && step.take <= s.num
}

ghost predicate NextStep(s: State, s': State, step: Step) {
  && ValidMove(step, s)
  && s'.num == s.num - step.take
  && s'.player1 == !s.player1
}

ghost predicate Next(s: State, s': State) {
  exists step: Step :: NextStep(s, s', step)
}

ghost predicate GameOver(s: State) {
  s.num == 0
}

ghost predicate Player1Win(s: State) {
  && GameOver(s)
     // whoever can't make a move on their turn loses
  && !s.player1
}

/*
ghost predicate IsPlay(play: seq<State>) {
  && |play| > 0
  && (forall i: int :: 0 <= i < |play|-1 ==> Next(play[i], play[i+1]))
  && GameOver(play[|play|-1])
}
*/

ghost predicate CurrentPlayerWins(s: State) {
  s.num % 11 != 0
}

ghost predicate CurrentPlayerLoses(s: State) {
  !CurrentPlayerWins(s)
}

// If the game is over, CurrentPlayerLoses/CurrentPlayerWins are correct. This
// is the "bottom" of the back and forth of the two lemmas below.
lemma WinnerAtEnd(s: State)
  requires GameOver(s)
  ensures CurrentPlayerLoses(s) && !CurrentPlayerWins(s)
  ensures Player1Win(s) <==> !s.player1
{}

// CurrentPlayerWins is correct in that there is a move that forces a loss for
// the next player
lemma CurrentPlayerWins_Next(s: State) returns (move: Step)
  requires CurrentPlayerWins(s)
  ensures ValidMove(move, s);
  ensures forall s' :: NextStep(s, s', move) ==> CurrentPlayerLoses(s')
{
  move := Step(s.num % 11);
}

// CurrentPlayerLoses is correct in that whatever the player does, the next
// player wins
lemma CurrentPlayerLoses_Next(s: State, s': State)
  requires CurrentPlayerLoses(s)
  requires Next(s, s')
  ensures CurrentPlayerWins(s')
{}

lemma HundredStart()
  // if player1 starts, they will win
  ensures CurrentPlayerWins(State(100, true))
{}
