axioms
(T:Type)
(Q:Prop)
(t:T)


example:(∀ (t : T), Q)→ Q :=
begin
assume h,
apply h t,
end




