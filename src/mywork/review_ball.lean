axioms
(Ball:Type)
(blue : Ball → Prop)
(allBallsBlue : ∀ (b:Ball), blue b)
(tomsBall:Ball)
theorem tomsBallIsBlue : blue tomsBall :=
  allBallsBlue tomsBall
--use proof of forall by applying

def ev(n:ℕ):=n%2=0
def odd(n:ℕ):=n%2=1

--predicates ev odd

def successor_of_even_is_odd : Prop :=
  ∀(n:ℕ), ev n → odd (n+1)

  axioms (raining streets_wet :Prop)
  axiom if_raining_then_streets_wet:raining → streets_wet

  axiom pf_raining : raining
  example : streets_wet := if_raining_then_streets_wet pf_raining
  --elim rule for → (APPLY IT)
  --intro rule for → (ASSUME IT)
  --communtative P and Q = Q and P
  --associative shift groupings
  --lean assumes AND is right associative