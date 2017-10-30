Inductive day : Type :=
  | monday : day
  | thuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day
  .

Definition next (d : day) : day :=
  match d with
  | monday    => thuesday
  | thuesday  => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

Compute (next friday).
Compute (next (next saturday)).
