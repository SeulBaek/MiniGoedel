(** In _Satan, Cantor, and Infinity_, Raymond Smullyan shows that we can express Goedel sentences, undecidable sentences, fixed points, and many other self-referential sentences in a language with only four symbols. Its minimalism makes for a good exercise for Coq beginners. Here's a step-by-step implementation and partial proof automation of the language, interspersed with the original text (in italics). *)

Require Import List Omega Classical Coq.Arith.Div2 LibTactics.
Import ListNotations.

(** The [LibTactics] library from _Software Foundations_(http://www.cis.upenn.edu/~bcpierce/sf/current/LibTactics.html) is used for its useful [jauto] and [iauto] tactics. *)

(* *)

(** # <i> "TODAY," said the Sorcerer, "I want to show you a miniature version of Goedel's famous incompleteness theorem. It will serve as a bridge from what we did last time to what we'll get into a bit later. The system I will now present is a modernized and streamlined version of a Smullyan 'language,' I shall use the quotationless method I showed you last time in place of Smullyan's one-sided quotation. "In the system, various sentences can be proved. The system uses the four symbols P, P*, Q, Q*." </i> # *)

Inductive symbol : Type := p | q | P | Q.

(** The symbols use slightly different characters for code legibility. Uppercase indicates duplicative symbols. *)

(* *)

(** # <i> "The symbol P means provability in the system - thus, for any expression X in the language of the system, PX asserts that X is provable in the system and accordingly will be called <b>true</b> if and only if X is provable in the system. The symbol Q stands for nonprovability in the system and for any expression X, QX asserts that X is not provable in the system and QX is called <b>true</b> just in the case that X is not provable in the system. Next, P*X means that XX is provable in the system, and is accordingly <b>true</b> if and only if this is the case. Lastly, Q*X means that XX is not provable in the system, and is called <b>true</b> if and only if XX is not provable in the system. By a <b>sentence</b> is meant any expression of one of the four forms PX, P*X, QX, Q*X, where X is any combination of the four symbols." </i> # *) 

Definition sentence : Type := list symbol.

(** # <i> "I henceforth use the word <b>provable</b> to mean provable in the system. Let us review the basic facts." </i> #

- # <i> (1) PX asserts that X is provable. </i> # 
- # <i> (2) QX asserts that X is not provable. </i> #  
- # <i> (3) P*X asserts that XX is provable. </i> # 
- # <i> (4) Q*X asserts that XX is not provable. </i> # 

# <br><i> "We see that the system is self-referential in that it proves various sentences that assert what the system can and cannot prove." </i> # *)

Variable true : sentence -> Prop.

Notation "'provable' X" := (true (p :: X))
(at level 60). 

(** Truth is primitive, and provability is defined in terms of truth. The converse is also possible, but it makes [true X] unfold in a messy way (it depends on the first symbol of [X]). We can also make both [true] and [provable] primitive and define their relationship as an additional axiom, but it is more work for no obvious benefit. *)

Axiom Aq1 : forall (X : sentence),
true (q :: X) -> ~ provable X.
Local Hint Resolve Aq1.

Axiom Aq2 : forall (X : sentence),
~ provable X -> true (q :: X).
Local Hint Resolve Aq2.

Axiom AP1 : forall (X : sentence),
true (P :: X) -> provable (X ++ X).
Local Hint Resolve AP1.

Axiom AP2 : forall (X : sentence),
provable (X ++ X) -> true (P :: X). 
Local Hint Resolve AP2.

Axiom AQ1 : forall (X : sentence),
true (Q :: X) -> ~ provable (X ++ X).
Local Hint Resolve AQ1.

Axiom AQ2 : forall (X : sentence),
~ provable (X ++ X) -> true (Q :: X). 
Local Hint Resolve AQ2.

(** These axioms correspond to the semantics of Q, P*, and Q*. Although their natural form is biconditional, they are split into conditionals to let [auto] apply them automatically. *)

(* *)

(** # <i> "We are given that the system is wholly accurate in that every sentence provable in the system is true - in other words the following four conditions hold (where X is any expression)." </i> #

- # <i> C1: If PX is provable so is X. </i> #
- # <i> C2: If QX is provable then X is not provable. </i> # 
- # <i> C3: If P*X is provable so is XX. </i> # 
- # <i> C4: If Q*X is provable then XX is not provable. </i> # *)

Axiom C1 : forall (X : sentence),
provable (p :: X) -> provable X.

Axiom C2 : forall (X : sentence),
provable (q :: X) -> ~ provable X.

Axiom C3 : forall (X : sentence),
provable (P :: X) -> provable (X ++ X).

Axiom C4 : forall (X : sentence),
provable (Q :: X) -> ~ provable (X ++ X).

(** Conditions C1-4 assert that MGL is sound (each consequent is equivalent to [true (H :: X)], where [H] is the head symbol in antecedent). If so, why not prove the general soundness claim [forall X : sentence, provable X -> true X]? This theorem would be useful for reasoning with sentences whose first symbol is unknown. 

We can't do it with C1-4, because [[]] is a [sentence] in our implementation. There are two ways around this. First, we can redefine [sentence] as an inductive type with eight constructors, giving a nullary and unary constructor to each symbol. This would ensure that every sentence is nonempty. It is much simpler, however, to add the axiom *)

Axiom ATN : true [].

(** with which we can show *)

Lemma LS1 : forall (X : sentence),
provable X -> true X.
intros. destruct X. apply ATN.
pose proof C1. pose proof C2. 
pose proof C3. pose proof C4.
destruct s; auto. Qed.
Hint Resolve LS1.

Lemma LS2 : forall (X : sentence),
~ true X -> ~ provable X.
auto. Qed. Hint Resolve LS2. 

(** [ATN] may be justified on the grounds that the truth of [[]] cannot be used to prove the truth/falsity of any nonempty sentence. This is clear from the fact that every sentence which occurs in other axioms is nonempty. The truth value we assign to [[]] is purely a matter of convenience.

Now we prove some lemmas that help automation. *)

Lemma HQq : forall (X : sentence),
true (Q :: X) -> true (q :: X ++ X).
auto. Qed. Local Hint Resolve HQq.

Lemma HqQ : forall (X : sentence),
true (q :: X ++ X) -> true (Q :: X).
auto. Qed. Local Hint Resolve HqQ.

Lemma HPQ : forall X,
~ true (P :: X) <-> true (Q :: X).
split. iauto. do 2 intro. apply (AQ1 X); 
iauto. Qed.

(** These lemmas provide shortcuts when making inferences between two sentences that start with [q], [P], and [Q]. *)

Lemma reuse_2 : forall P Q R : Prop, 
P -> Q -> (P -> Q -> R) -> (P /\ Q /\ R).
auto. Qed.

Lemma reuse_3 : forall P Q R S : Prop,
P -> Q -> R -> (P -> Q -> R -> S) 
-> (P /\ Q /\ R /\ S). auto. Qed.

Lemma not_imply_or : forall P Q : Prop,
(~ P -> Q) -> (P \/ Q).
intros. apply NNPP. iauto. Qed.

Lemma iff_neg : forall P Q,
( P <-> Q ) -> ( ~ P <-> ~ Q ).
intros. split; apply NNPP; iauto. Qed.

Lemma iff_trans : forall P Q R,
(P <-> Q) -> (Q <-> R) -> (P <-> R).
intros. iauto. Qed.

Theorem reductio_t : forall X,
( ~ true X -> true X ) -> true X.
intro. apply NNPP. auto. Qed.
Hint Resolve reductio_t.

Theorem reductio_np : forall X,
( provable X -> ~ provable X ) 
-> ~ provable X. auto. Qed.
Hint Resolve reductio_np. 

(** Some tautologies that introduce useful hypothese into context. Note that [reductio_t] requires [NNPP] of classical logic. 

We also need to fix a minor issue with pattern matching. Consider *)

Theorem auto_success : 
true [P;p] -> provable ([p] ++ [p]).
auto. Qed.

(** which [auto] can prove automatically, because [AP1] is available in the default hint database. Compare *) 

Theorem auto_fail : 
true [P;p] -> provable [p;p].
auto. Abort.

(** which is equivalent to [auto_success], but fails because [provable [p;p]] cannot be matched with the consequent of [AP1]. We need to give [auto] the ability to split up a conclusion [provable XX] into [provable (X ++ X)]. Here's one way to do it. *)

Lemma merge_p : forall (X : sentence),
provable ( firstn (div2 (length X)) X ++ 
skipn (div2 (length X)) X) -> provable X.
intros. rewrite firstn_skipn in H. auto. 
Qed. Local Hint Resolve merge_p.

Lemma merge_q : forall (X : sentence),
~ provable ( firstn (div2 (length X)) X ++
skipn (div2 (length X)) X) -> ~ provable X.
intros. rewrite firstn_skipn in H. auto. 
Qed. Local Hint Resolve merge_q.

(** We are now ready to tackle our first problem. *)

(* *)

(** # <i> "Now, just because every sentence provable in the system is true, it doesn't necessarily follow that every true sentence is provable in the system. As a matter of fact, there happens to be a sentence that is true but not provable in the system. Can you find it?" </i> # *)

(** # <center> <b> <i> * 1 * </i> </b> </center> # *)

(** # <center> <i> Find a true sentence that is not provable in the system. </i> </center> # *)

Theorem P1 : 
true [Q;Q] /\ ~ provable [Q;Q].
split; eauto. Qed.

(** # <i> <b>Refutable Sentences.</b> "For each sentence, we define its <b>conjugate</b> as follows. The conjugate of PX is QX, and the conjugate of QX is PX. The conjugate of P*X is Q*X and the conjugate of Q*X is P*X. Thus the sentences PX and QX are conjugates of each other, and the sentences P*X and Q*X are conjugates of each other. Given any conjugate pair, it is obvious that one of the pair is true and the other false. </i> # *)

Definition conjugate (X : sentence) :
sentence := match X with
| [] => []
| p :: X' => q :: X'
| q :: X' => p :: X'
| P :: X' => Q :: X'
| Q :: X' => P :: X'
end.

(** # <i> "A sentence is called <b>refutable</b> (in the system) if its conjugate is provable (in the system). Thus, PX is refutable if and only if QX is provable, and PX is provable if and only if QX is refutable. Likewise with P*X and Q*X." </i> # *)

Notation "'refutable' X" := (provable (conjugate X)) (at level 70).

(** # <center> <b> <i> * 2 *  </i> </b> </center> # *)

(** # <center> <i> Find a sentence that asserts that it is refutable. </i> </center> # *)

Theorem P2 : 
true [P;Q] <-> refutable [P;Q].
iauto. Qed.

(** # <center> <b> <i> * 3 * </i> </b> </center> # *)

(** # <center> <i> Find a sentence that asserts that it is not refutable. </i> </center> # *)

Theorem P3 : 
true [Q;P] <-> ~ refutable [Q;P].
split; eauto. Qed.

(** # <center> <b> <i> * 4 * </i> </b> </center> # *)

(** # <center> <i> What sentence asserts that it is provable? </i> </center> # *)

Theorem P4 :
true [P;P] <-> provable [P;P].
iauto. Qed.

(** # <i> <b>Undecidable Sentences.</b> "A sentence is called <b>undecidable</b> (in the system) if it is neither provable nor refutable in the system," said the Sorcerer. "Now, as you saw in the solution of Problem 1, the sentence Q*Q* is true but not provable in the system. Since it is true, then its conjugate P*Q* is false, hence also not provable in the system. Thus the sentence Q*Q* is undecidable in the system." </i> # *)

Notation "'undecidable' X" := 
(~ provable X /\ ~ refutable X)
(at level 65).

(** # <i> "My argument has appealed to the notion of truth, but even without appeal to this notion one can obtain the undecidability of Q*Q* as a direct consequence of conditions C1 through C4 as follows: Suppose were Q*Q* provable. Then by C4, taking Q* for X, the repeat of Q* is not provable, which means that Q*Q* is not provable. So if Q*Q* is provable, then it is not provable, which is a contradiction. Therefore, Q*Q* is not provable. If its conjugate P*Q* were provable, then by C3 (taking Q* for X) Q*Q* would be provable, which we just saw is not the case. And so P*Q* is not provable either. Thus the sentence Q*Q* is undecidable in the system." 
	
<br> <br> 

"Tell me this," said Annabelle. "Is Q*Q* the only sentence that is true but unprovable, or are there others?" 

<br> <br> 
	
"The sentence Q*Q* ," replied the Sorcerer, "is the only sentence that I know of having the property that for <b>every</b> system satisfying conditions C1 through C4, it is true for that system and unprovable in that system. But, as you will see later, for any system satisfying C1 through C4, there are other sentences that are true but unprovable in that system. The sentence Q*Q* is, as I said, the only sentence that I know that simultaneously works for <b>all</b> systems satisfying C1 through C4. </i> # *)

(* *) 

(** Another way to pose the question: Does [( MGL |- true X /\ ~ provable X ) => ( X = QQ )] hold for all [X]? It is an interesting problem, but its proof requires (among others) a definition of theoremhood in MGL, which we do not have in the current implementation. *)

(* *) 

(** # <i> The Sorcerer then gave the following problems: </i> # *)

(** # <center> <i> <b> 5 * Some Fixed-Point Properties </b> </i> </center> # *)

(** # <i> Show that for any expression E there is a sentence X that asserts that EX is provable (X is true if and only if EX is provable) and there is some X that asserts that EX is not provable. </i> # *)

Theorem P5A : forall E, exists X,
true X <-> provable (E ++ X).
intros. exists ([P] ++ E ++ [P]).
split; intros. rewrite app_assoc. auto. 
apply AP2. rewrite <- app_assoc. auto. Qed.

Theorem P5B : forall E, exists X,
true X <-> ~ provable (E ++ X).
intros. exists ([Q] ++ E ++ [Q]).
split; intros. 
rewrite app_assoc. auto. apply AQ2. 
rewrite <- app_assoc. auto. Qed.

(** # <center> <i> <b> 6 * Some Anti-Fixed-Point Properties </b> </i> </center> # *)

(** # <i> For any sentence X, let -X be the conjugate of X. </i> # *)
	
(** # <i> Show that for any expression E there is some sentence X that asserts that E-X is provable and a sentence X that asserts that E-X is not provable. </i> # *)

Theorem P6A : forall E, exists X,
true X <-> provable (E ++ conjugate X).
intros. exists ([P] ++ E ++ [Q]).
split; intros. simpl in *. apply AP1 in H. 
rewrite <- app_assoc in H. auto. 
apply AP2. rewrite <- app_assoc. auto. 
Qed.  

Theorem P6B : forall E, exists X,
true X <-> ~ provable (E ++ conjugate X).
intros. exists ([Q] ++ E ++ [P]).
split; intros. apply AQ1 in H. 
rewrite <- app_assoc in H. auto. 
apply AQ2. simpl in H. 
rewrite <- app_assoc. auto. Qed.  

(** # <i> Next, the Sorcerer presented some problems in cross-reference.</i> # *)

(* *)

(** Problems 7-11 have the form [exists X Y ... : setence, A /\ B], where [A] logically entails [B]. We exploit this pattern by proving [forall X Y ... : sentence, A -> B] as a separate lemma, which is easier than proving [B] independently for specific sentences. *) 

(** Proving theorems of the form [forall X Y ... : sentence, A -> B] requires the ability to reason about the relationship between truth and refutability of arbitrary sentences. Again, [[]] is a minor issue here. We need an additional axiom *)

Axiom ANPN : ~ provable [].

(** [ANPN] is justified for the same reason as [ATN], although it's not as obvious that this is the case. [ANPN] is equivalent to [~ true [p]], from which you can derive [~ true [P]], [true [q]], [true [Q]], and nothing else. Since none of these propositions occur in the chapter, the truth of [ANPN] is also a matter of convenience. 
	
With [ANPN], we can make some obvious modal inferences. *)

Lemma true_irrefutable : 
forall X, true X -> ~ refutable X.
do 3 intro. destruct X. apply ANPN. auto. 
destruct s; lets : C1; lets : Aq1; 
lets : AQ1; jauto. Qed.

Lemma refutable_false : 
forall X, refutable X -> ~ true X.
lets : true_irrefutable. jauto. Qed.

(** # <center> <b> <i> * 7 * </i> </b> </center> # *)

(** # <i> Find sentences X and Y such that X asserts that Y is provable and Y asserts that X is not provable. (There are two solutions.) Then show that at least one of the sentences X, Y must be true but not provable (though there is no way to tell which). </i> # *)

Theorem P7L : forall X Y, 
( true X <-> provable Y )
-> ( true Y <-> ~ provable X )
-> ( ( true X /\ ~ provable X ) 
   \/ ( true Y /\ ~ provable Y ) ).   
repeat (intros; try apply not_imply_or). 
lets : true_irrefutable; lets : refutable_false; iauto. Qed. 

Notation X7 := ([p;Q;p;Q]).
Notation Y7 := ([Q;p;Q]).

Theorem P7 : 
( true X7 <-> provable Y7 )
/\ ( true Y7 <-> ~ provable X7 )
/\ ( ( true X7 /\ ~ provable X7 ) 
   \/ ( true Y7 /\ ~ provable Y7 ) ).   
apply reuse_2. splits; eauto. 
splits; eauto. apply P7L; intro; false.
Qed. 

(** # <center> <b> <i> * 8 * </i> </b> </center> # *)

(** # <i> Now find sentences X and Y such that X asserts that Y is refutable and Y asserts that X is not refutable. (There are two solutions.) Then show that at least one of the two must be false but not refutable (though there is no way to tell which). </i> # *)

Theorem P8L : forall X Y,
( true X <-> refutable Y )
-> ( true Y <-> ~ refutable X )
-> ( ( ~ true X /\ ~ refutable X ) 
   \/ ( ~ true Y /\ ~ refutable Y ) ).  
repeat (intros; try apply not_imply_or). 
lets : true_irrefutable; lets : refutable_false; iauto. Qed. 

Notation X8 := ([p;P;q;P]). 
Notation Y8 := ([Q;q;P]). 

Theorem P8 : 
( true X8 <-> refutable Y8 )
/\ ( true Y8 <-> ~ refutable X8 )
/\ ( ( ~ true X8 /\ ~ refutable X8 ) 
   \/ ( ~ true Y8 /\ ~ refutable Y8 ) ).  
apply reuse_2. splits; eauto. split; eauto.
apply P8L. Qed.

(** # <center> <b> <i> * 9 * </i> </b> </center> # *)

(** # <i> Find sentences X and Y such that X asserts that Y is provable and Y asserts that X is refutable. (There are two solutions.) Then show that one of them is true and not provable, or the other is false but not refutable. Which of X, Y is which? </i> # *)

Theorem P9L : forall X Y,
( true X <-> provable Y )
-> ( true Y <-> refutable X )
-> ( ( ~ true X /\ ~ refutable X ) 
   \/ ( true Y /\ ~ provable Y ) ).
repeat (intros; try apply not_imply_or). 
lets : true_irrefutable; lets : refutable_false; split; 
[apply NNPP|]; iauto. Qed.

Notation X9 := [P;p;Q]. 
Notation Y9 := [p;Q;p;Q]. 

Theorem P9 : 
( true X9 <-> provable Y9 )
/\ ( true Y9 <-> refutable X9 )
/\ ( ( ~ true X9 /\ ~ refutable X9 ) 
   \/ ( true Y9 /\ ~ provable Y9 ) ).
apply reuse_2. splits; iauto. 
splits; iauto. apply P9L. Qed.

(** # <center> <b> <i> * 10 * </i> </b> </center> # *)

(** # <i> Find sentences X and Y such that X asserts that Y is not provable and Y asserts that X is not refutable. Does it follow that one of them must be undecidable? </i> # *)

Theorem P10L : forall X Y,
( true X <-> ~ provable Y )
-> ( true Y <-> ~ refutable X )
-> ( undecidable X \/ undecidable Y ).
repeat (intros; try apply not_imply_or). 
lets : true_irrefutable; lets : refutable_false. iauto. Qed.

Notation X10 := [Q;q;P]. 
Notation Y10 := [q;P;q;P]. 

Theorem P10 : 
( true X10 <-> ~ provable Y10 )
/\ ( true Y10 <-> ~ refutable X10 )
/\ ( undecidable X10 \/ undecidable Y10 ).
apply reuse_2. split; eauto. 
split; eauto. apply P10L. Qed.

(** # <center> <b> <i> * 11 * </i> </b> </center> # *)

(** # <i> Find sentences X, Y, and Z such that X asserts that Y is refutable, Y asserts that Z is not refutable and Z asserts that X is provable. Is one of the three necessarily undecidable? </i> # *)

Theorem P11L : forall X Y Z,
( true X <-> refutable Y )
-> ( true Y <-> ~ refutable Z )
-> ( true Z <-> provable X )
-> ( undecidable X \/ undecidable Y 
   \/ undecidable Z ).
intros. repeat (apply not_imply_or; intro).
lets : true_irrefutable; lets : refutable_false. iauto. Qed.

Notation X11 := [p;p;Q;p;p;Q].
Notation Y11 := [q;Q;p;p;Q]. 
Notation Z11 := [P;p;p;Q].

Theorem P11 : 
( true X11 <-> refutable Y11 )
/\ ( true Y11 <-> ~ refutable Z11 )
/\ ( true Z11 <-> provable X11 )
/\ ( undecidable X11 \/ undecidable Y11 
   \/ undecidable Z11 ).
apply reuse_3. split; eauto. split; eauto. 
split; eauto. apply P11L. Qed. 

(** # <center> <b> <i> * 12 * </i> </b> </center> # *)

(** # <i> "I have said before," said the Sorcerer, "that for any system satisfying conditions C1 through C4, there are sentences other than that are true but unprovable in the system. You are now in a position to prove this. Do you see how?" </i> # *)

Theorem P12 : exists X, X <> [Q;Q] 
/\ true X /\ ~ provable X.
lets : P7. destruct H. destruct H0.  
do 2 (destruct H1); [ exists X7 |
exists Y7 ]; splits; iauto; intro; 
inversion H3. Qed.

(** # <i> "I shall call a system <b>regular</b>," said the Sorcerer, "if the converses of conditions C1 and C3 hold - that is, if X is provable, so is PX and if XX is provable, so is P*X. This together with C1 and C3 tell us that PX is provable if and only if X is provable, and P*X is provable if and only if XX is provable. I might remark that regularity is the analogue of a condition that does hold for the type of systems studied by Goedel, but I'll say more about that another time. Regular systems have some interesting properties, as you will soon see. </i> # *)

(** # <i> "Let me define a <b>positive</b> sentence as one of the form PX or P*X and a negative sentence as one of the form QX or X. Positive sentences assert that certain sentences are provable; negative sentences assert that certain sentences are not provable. Let us now note that if the system is regular, then all true positive sentences are provable, and conversely, if all true positive sentences are provable, then the system is regular." </i> # *)

Notation C1C := (forall X, 
provable X -> provable (p :: X)).

Notation C3C := (forall X, 
provable (X ++ X) -> provable (P :: X)).

Definition regular := C1C /\ C3C.

Inductive positive : sentence -> Prop :=
| pos : forall X, positive (p :: X)
| Pos : forall X, positive (P :: X).
Hint Constructors positive.

Inductive negative : sentence -> Prop :=
| neg : forall X, negative (q :: X)
| Neg : forall X, negative (Q :: X).
Hint Constructors negative.

(** # <center> <b> <i> * 13 * </i> </b> </center> # *)

(** # <i> Why is it that the system is regular if and only if all true positive sentences are provable? </i> # *)

Theorem P13 : regular <-> forall X, 
positive X -> true X -> provable X.
unfold regular; split; intros.
destruct H; inverts H0; jauto. 
split; intros; apply H; auto. Qed.

Theorem P13C : regular <-> forall X, 
positive X -> ~ provable X -> ~ true X. 
split; intros. lets : P13. 
destruct H2. pose proof (H2 H).
iauto. apply P13. intros. 
apply NNPP. jauto. Qed.

(** # <i> "And so," continued the Sorcerer, "we see that in a regular system, only negative sentences can be true but unprovable. Any sentence that asserts that something is provable, if true, must itself be provable." </i> # *)

(** # <center> <b> <i> * 14 * </i> </b> </center> # *)

(** # <i> If a system is regular, does it necessarily follow that every false negative sentence is refutable? </i> # *)

Theorem P14 : regular -> forall X, 
negative X -> ~ true X -> refutable X.
unfold regular. intros. inverts H0. 
apply H. apply NNPP. iauto.
apply H. apply NNPP. iauto.
Qed.

Theorem P14C : regular -> forall X, 
negative X -> ~ refutable X -> true X.
intros. lets : P14. apply NNPP. iauto. 
Qed.

(** # <i> "Regular systems have some interesting features," said the Sorcerer, "as you will now see." </i> # *)

(** # <center> <b> <i> * 15 * </i> </b> </center> # *)

(** # <i> "For one thing, in a regular system, the ambiguities of Problems 7 through 10 disappear - that is, if we assume the system is regular, then in Problem 7 we can tell whether it is X or Y that is true but unprovable. Which is it? And in Problem 8, is it X or Y that is false but not refutable? And for Problem 9, is it X that is true but provable, or is it Y that is false but not refutable? And for Problem 10, is it X that is undecidable? All this, of course, with the assumption of regularity." </i> # *)

Theorem P15A : 
regular -> true Y7 /\ ~ provable Y7.
lets : P7. lets : P13. iauto. Qed.

Theorem P15B : 
regular -> ~ true X8 /\ ~ refutable X8.
lets : P8. lets : P14. iauto. Qed.

Theorem P15C : 
regular -> ~ true X9 /\ ~ refutable X9. 
lets : P9. lets : P13. iauto. Qed.

Theorem P15D : 
regular -> undecidable Y10.
lets : true_irrefutable. lets : P10. lets : P14. 
iauto. Qed.

(** While making this tutorial, I noticed that regularity also eliminates ambiguity for P11. Although not part of the original text, it is an obvious extension, so I include it here. *)

Theorem P15E : 
regular -> undecidable Z11.
lets : P11. lets : P13. lets : P14. 
intro. destruct H. destruct H3. 
destruct H4. inverts H5.
assert (~ true X11 /\ ~ true Z11 
/\ ~ refutable Y11 ). splits; iauto.
iauto. inverts H6.
assert (true Y11 /\ ~ true Z11).
splits; iauto. iauto. auto. Qed.

(** # <i> "Let us note," said the Sorcerer, "that for any system satisfying our given conditions C1 through C4, whether the system is regular or not, if E is any string of P's, then if EX is provable, so is X. This follows by repeated applications of C1. For example, if PPPX is provable, so is PPX (by C1); hence so is PX (again by C1); hence so is X (again by C1). You can readily see that the same holds if E contains four or more P's—or if E contains two P's or just one P. And so if E is any string of P's, if EX is provable, so is X. For a regular system, the converse also holds - that is, if X is provable, so is EX, where E is any string of P's. For if X is provable and the system is regular, then PX is provable (by regularity); hence so is PPX, and so forth. And so for a regular system, if E is any string of P's, then EX is provable if and only if X is provable. </i> # *)

(** # <i> "Another thing about regular systems is this: For any system satisfying C1 through C4, P*X is true if and only if PXX is true, for each is true if and only if XX is provable. However, without regularity, there is no reason to believe that P*X is provable if and only if PXX is provable. If either one is provable, then the other one is true, but that doesn't mean that the other one is provable. However, if the system is regular, then P*X is provable if and only if PXX is provable." </i> # *)

(** # <center> <b> <i> * 16 * </i> </b> </center> # *)

(** # <i> Why is it that in a regular system, P*X is provable if and only if PXX is provable? </i> # *)

Theorem P16 : regular -> forall X, 
( provable ( P :: X ) 
<-> provable ( p :: X ++ X ) ).
intros. lets : P13. split; iauto. Qed.

(** # <i> "Now comes a particularly interesting thing about regular systems," said the Sorcerer. "We have already seen that in any system satisfying conditions C1 through C4, there are infinitely many sentences that are true for the system but not provable in the system. But this does not mean that there are infinitely many sentences such that each one is true for <b>all</b> systems satisfying C1 through C4 and at the same time unprovable for <b>all</b> such systems. However, there are infinitely many sentences X such that for every <b>regular</b> system satisfying C1 through C4, each X is true for the system but unprovable in the system." </i> # *)

(** # <center> <b> <i> * 17 * </i> </b> </center> # *)

(** # <i> Can you prove this? </i> # *)

(* *)

(** We first need some way to express infinity in Coq. The easiest way is to demonstrate countable infinity by an injective function from natural numbers. *)

Definition injective {X Y : Type} 
(f : X -> Y) := 
forall x y : X, f x = f y -> x = y.

Definition infinite (X : Type) 
(P : X -> Prop) := 
exists (f : nat -> X), 
injective f /\ forall n, P (f n).

(** [infinite X P] asserts that there are an infinite number of [X]s that have property [P]. 
To define our injective function, use the fact that QXP*QXP* is a true unprovable sentence in any regular system, where X is any number of consecutive Ps. *) 

Fixpoint pstring (n : nat) : sentence :=
match n with
| 0    => []
| S n' => p :: pstring n'
end.

Definition goedel (n : nat) : sentence :=
( [q] ++ pstring n ++ [P] ) 
++ ( [q] ++ pstring n ++ [P] ).

(** [goedel] is our desired function. Its injectivity can be proved from the fact that different arguments to [goedel] always produce sentences of different lengths. *)

Theorem goedel_length : forall n,
length (goedel n) = 4 + (2 * n).
induction n. auto. unfold goedel in *.
repeat (rewrite app_length in *).
simpl in *. omega. Qed.

Theorem goedel_inj : injective goedel.
unfold injective. intros. 
apply (f_equal (@length symbol)) in H. 
repeat (rewrite goedel_length in H).
omega. Qed.

(** Lemmas P17L1-6 prove that [goedel n] is true and unprovable in all regular systems for any [n]. *)

Lemma P17L1 : forall n X,
positive X -> positive (pstring n ++ X).
intros. destruct n; simpl; auto. Qed.

Theorem P17L2 : 
regular -> forall n X, 
(true ( ( pstring n ) ++ P :: X) 
<-> true (P :: X)).
intros. induction n. split; intro; iauto. 
simpl. lets : P13. lets : P17L1. split; iauto. Qed. 

Theorem P17L3 :
regular -> forall n X, 
( true ( [q] ++ pstring n ++ [P] ++ X )
<-> ~ true ( pstring n ++ [P] ++ X) ).
intros; split; intro. apply P13C; auto. 
apply P17L1; auto. simpl. auto. simpl.
auto. Qed.

Theorem P17L4 :
regular -> forall n X, 
( true ( [q] ++ pstring n ++ [P] ++ X ) 
<-> true ( Q :: X ) ).
intros. apply iff_trans with 
( ~ true ( pstring n ++ [P] ++ X) ). 
apply P17L3; auto. apply iff_trans with 
( ~ true ( P :: X) ). apply iff_neg. 
apply P17L2; iauto. apply HPQ. Qed.  

Theorem P17L5 : forall X,
( true ( X ++ X ) <-> true ( Q :: X ) ) ->
true ( X ++ X ) /\ ~ provable ( X ++ X ).
intros; split; iauto. apply reductio_np. 
intro. apply AQ1. iauto. Qed.

Theorem P17L6 : regular -> forall n, 
true (goedel n) /\ ~ provable (goedel n).
intros. unfold goedel. apply P17L5. 
repeat rewrite <- app_assoc. apply P17L4; 
auto. Qed.

Theorem P17 : regular -> infinite sentence
( fun X => true X /\ ~ provable X ). 
intro. exists goedel. split. apply 
goedel_inj. apply P17L6. auto. Qed.

(** # <i> "What I have shown you today," said the Sorcerer, "has applications to the field known as <b>metamathematics</b> - the theory of mathematical systems. My miniature system provides one approach to Goedel's famous incompleteness theorem: </i> # *)

(** # <i> "Let us consider a mathematical system (M) in which there are well-defined rules specifying certain sentences as true and others as provable in (M), and suppose that we wish to know whether (M) is <b>complete</b> in the sense that all true sentences of (M) are provable in (M). Now it can be shown that if (M) is any one of a wide variety of systems investigated by Kurt Goedel, it is possible to <b>translate</b> my system into (M) in the sense that corresponding to each sentence X of my system, there is a sentence X* of the system (M) such that X is true in my system if and only if the corresponding sentence X* of (M) is a true sentence of (M), and also, X is provable in my system if and only if X* is provable in (M). Do you realize the ramifications of this? It means that for every such system (M), there must be a true sentence of (M) that is not provable in (M) - its truth can be known only by going outside of the system. Thus, no system (M) into which my system is translatable can possibly be complete. Do you see why this is so?" </i> # *)

(** # <center> <b> <i> * 18 * </i> </b> </center> # *)

(** # <i> Why is this so? </i> # *)

(* *)

(** A reasonable assumption in formalizing P18 is that M-sentences are a type, and M-truth and M-provability are predicates on that type. Then we can define traslatability as *)

Inductive translatable (Msentence : Type) 
(Mtrue : Msentence -> Prop)  
(Mprovable : Msentence -> Prop) : Prop := 
| trnsl : ( forall (X : sentence), 
  exists (X0 : Msentence), 
  ( Mtrue X0 <-> true X )
  /\ ( Mprovable X0 <-> provable X ) )
  -> (translatable Msentence 
      Mtrue Mprovable) .

(** from which P18 easily follows. *)

Theorem P18 : 
forall Msentence Mtrue Mprovable,  
(translatable Msentence Mtrue Mprovable) 
-> exists (X0 : Msentence),
Mtrue X0 /\ ~ Mprovable X0.
intros. inverts H. pose proof (H0 [Q;Q]). 
inverts H. exists x. split; lets : P1; 
iauto. Qed.

(** # <i> All this is most remarkable!" </i> # *)

(** # <i> "It certainly is!" agreed Alexander. </i> # *)

(** # <i> "What will you tell us about next time?" asked Annabelle. </i> # *)

(** # <i> "On your next visit," replied the Sorcerer with a mischievous smile, "I have a very special paradox prepared for you." </i> # *)

(** # <i> "I'm looking forward to it," said Annabelle. "I've always been intrigued by paradoxes." </i> # *)
