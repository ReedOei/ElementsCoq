Require Import Ensembles Field.

Module Type Geometry.

Import Field_theory.

(* The type representing the "Length" of a line segment. Should be a (ordered) field *)
Parameter Length : Type.
Parameter (lO lI : Length) (ladd lmul lsub: Length -> Length -> Length) (lopp : Length -> Length).
Parameter (ldiv : Length -> Length -> Length) (linv : Length -> Length).
Parameter Length_eq : Length -> Length -> Prop.
Parameter Length_lt : Length -> Length -> Prop.
Parameter Length_field : field_theory lO lI ladd lmul lsub lopp ldiv linv Length_eq.

Parameter Point : Type.
Parameter Angle : Type.

(* Notation to make working with lengths easier *)
Notation "0" := lO.
Notation "1" := lI.
Infix "+" := ladd.
Infix "-" := lsub.
Infix "*" := lmul.
Infix "/" := ldiv.
Notation "- x" := (lopp x).
Notation "x ^ -1" := (linv x) (at level 17).

Notation "a < b" := (Length_lt a b).
Notation "a <= b" := (Length_lt a b \/ a = b).

Parameter Length_add_increases : forall (x y z : Length), x <= z -> x <= z + y.

Lemma Length_lte_refl : forall {l : Length}, l <= l.
Proof.
intuition.
Qed.

(* Axiom 1: A straight line segment can be drawn joining any two points. *)
Definition LineSegment : Type := Point * Point.
Parameter length : LineSegment -> Length.

Parameter length_mag : forall (a b : Point), length (a, b) = length (b, a).

Definition Circle := Ensemble Point.

(* All circles have both a center and a radius *)
Parameter center : Circle -> Point.
Parameter radius : Circle -> Length.

(* A radius is a line segment starting at the center of the circle and ending somewhere on the circle *)
Definition is_radius (l : LineSegment) (c : Circle) :=
  match l with
  | (a, b) => a = center c /\ c b
  end.

(* Axiom 3: Given any straight line segment, a circle can be drawn having
            the segment as radius and one endpoint as center. *)
Axiom circle :
  forall (a b : Point),
    exists (c : Circle), is_radius (a, b) c.

(* Every circle is has at least a single point in it *)
Axiom circle_has_point : forall (c : Circle), {p : Point | In Point c p}.

Lemma exists_radius : forall (c : Circle), exists (p : Point), is_radius (center c, p) c.
Proof.
intuition.
destruct (circle_has_point c).
exists x.
unfold is_radius.
intuition.
Qed.

Parameter radius_length :
  forall (c : Circle) (p : Point),
    is_radius (center c, p) c -> radius c = length (center c, p).

(* Definition: For any circle, every point has the same distance to the center *)
Axiom radius_equal : forall (c : Circle) (a b : Point),
  c a /\ c b <-> length (center c, a) = length (center c, b).

Definition OnLine (l : Line) := { seg : LineSegment | let (a, b) := seg in l a /\ l b }.

(* Axiom 2: Any straight line segment can be extended indefinitely in a straight line. *)
Axiom line : LineSegment -> Line.

(* Some angles are Right angles, some are not. *)
Parameter Right : Angle -> Prop.

(* Relation that two lines are parallel *)
Parameter Parallel : Line -> Line -> Prop.

(* Intersection definition:
    (i) Two lines intersect at every point iff they are the same line.
    (ii) Two lines are not the same line iff they intersection at 1 or 0 points. *)
Axiom intersection_def :
  forall (a b : Line),
    (a = b <-> Intersection Point a b = a) /\
    (~(a = b) <-> Intersection Point a b = Empty_set Point \/
                  exists (x : Point), Intersection Point a b = Singleton Point x).

(* If two circles have the same center, they're either the same circle, or they have no points in common *)
Axiom same_center_intersection :
  forall (c1 c2 : Circle),
    center c1 = center c2 ->
      ((Same_set Point c1 c2 -> Intersection Point c1 c2 = c1) /\
       (~(Same_set Point c1 c2) -> Intersection Point c1 c2 = Empty_set Point)).

(* If two circles do not have the same center, they either intersect at 2 or 0 points *)
Axiom dif_center_intersection :
  forall (c1 c2 : Circle),
    ~(center c1 = center c2) ->
        let intersect := Intersection Point c1 c2 in
        let rtot := radius c1 + radius c2 in
        let dist := length (center c1, center c2) in
          (dist <= rtot -> exists (i1 i2 : Point), intersect = Couple Point i1 i2) /\
          (~(dist <= rtot) -> intersect = Empty_set Point).

Definition equilateral (a b c : Point) : Prop :=
  length (a, b) = length (b, c) /\
  length (b, c) = length (a, c).

Notation "a || b" := (Parallel a b).

Axiom parallel : forall (a b : Line), a || b <-> Intersection Point a b = Empty_set Point.

(* Axiom 4: All right angles are congruent. *)
Axiom right_angles : forall (a b : Angle), Right a /\ Right b -> a = b.

Lemma neq_sym : forall (A : Type) (a b : A), a <> b <-> b <> a.
Proof.
intuition.
Qed.

Lemma pair_equal_temp : forall (A B : Type) (p1 p2 : A * B), p1 = p2 -> fst p1 = fst p2 /\ snd p1 = snd p2.
Proof.
intuition.
destruct H.
reflexivity.
destruct H.
reflexivity.
Qed.

Lemma pair_equal :
  forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
    (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.
intuition.
destruct (pair_equal_temp A B (a1, b1) (a2, b2) H).
unfold fst in H0.
assumption.
destruct (pair_equal_temp A B (a1, b1) (a2, b2) H).
unfold snd in H1.
assumption.
rewrite H0, H1.
reflexivity.
Qed.

Lemma length_eq_radius_is_radius :
  forall (c : Circle) (a : Point),
    length (center c, a) = radius c -> is_radius (center c, a) c.
Proof.
intuition.
unfold is_radius.
split.
reflexivity.
destruct (exists_radius c).
pose proof radius_length c x H0.
destruct (radius_equal c a x).
rewrite H in H3.
exact (proj1 (H3 H1)).
Qed.

Lemma length_of_radius :
  forall (c : Circle) (a : Point),
    is_radius (center c, a) c -> length (center c, a) = radius c.
Proof.
intuition.
unfold is_radius.
destruct H.
destruct (exists_radius c).
pose proof radius_length c x H1.
destruct (radius_equal c a x).
destruct H1.
rewrite <- H2 in H3.
exact (H3 (conj H0 H5)).
Qed.

Lemma segment_defines_two_circles :
  forall (a b : Point), a <> b ->
    exists (c1 c2 : Circle) (i1 i2 : Point),
      is_radius (a, b) c1 /\
      is_radius (b, a) c2 /\
      Intersection Point c1 c2 = Couple Point i1 i2.
Proof.
intuition.

(* Create the two circles *)
pose proof (circle a b).
destruct H0. destruct H0.
exists x.
pose proof (circle b a).
destruct H2. destruct H2.
exists x0.

(* Show that their centers are not equal *)
rewrite H0, H2 in H.

(* Build the intersection of the two circles *)
pose proof dif_center_intersection x x0 H.
destruct H4. destruct H4.
rewrite <- H0, <- H2.
pose proof length_of_radius x b.
rewrite <- H0 in H4.
pose proof H4 (conj H0 H1).
rewrite H6.
exact (Length_add_increases (radius x) (radius x0) (radius x) Length_lte_refl).
destruct H4.

(* Use the intersection we built *)
exists x1. exists x2.
intuition.
exact (conj H0 H1).
exact (conj H2 H3).
Qed.

Lemma both_circles_same_radius :
  forall {c1 c2 : Circle} {a b : Point},
    is_radius (a, b) c1 -> is_radius (b, a) c2 -> radius c1 = radius c2.
Proof.
intuition.
destruct H.
destruct H0.
pose proof radius_length c1 b (conj eq_refl H1).
pose proof radius_length c2 a (conj eq_refl H2).
rewrite H3, H4, H0, H.
apply length_mag.
Qed.

Lemma point_defines_radius :
  forall (c : Circle) (a : Point), In Point c a -> is_radius (center c, a) c.
Proof.
intuition.
unfold is_radius.
intuition.
Qed.

Lemma radius_length_equal :
  forall {c1 c2 : Circle} {a b c d : Point},
    radius c1 = radius c2 -> is_radius (a,b) c1 -> is_radius (c,d) c2 -> length (a,b) = length(c,d).
Proof.
intuition.
destruct H0. destruct H1.
pose proof radius_length c1 b (conj eq_refl H2).
pose proof radius_length c2 d (conj eq_refl H3).
rewrite <- H0 in H4.
rewrite <- H1 in H5.
rewrite <- H4, <- H5.
assumption.
Qed.

Proposition prop_1 :
  forall (p p0 : Point),
      p <> p0 -> exists (c : Point), equilateral p p0 c.
Proof.
intuition.

(* Get the common points of the two circles defined by (p,p0) and
   pick one arbitrarily to be the third point of the triangle *)
pose proof segment_defines_two_circles p p0 H.
destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
exists x1.
unfold equilateral.

(* Prove that the lengths are the same. First we need to show the point x1 is in both circles *)
pose proof Couple_l Point x1 x2.
rewrite <- H2 in H3.
destruct H3.

split.

(* Prove that length (p, p0) = length (p0, x1) *)
destruct H0.
pose proof point_defines_radius x p0 H5.
rewrite <- H0 in H6.

destruct H1.
pose proof point_defines_radius x0 x1 H4.
rewrite <- H1 in H8.

pose proof both_circles_same_radius H6 (conj H1 H7).
exact (radius_length_equal H9 H6 H8).

(* Prove that length (p0, x1) = length (p, x1) *)
destruct H0.
pose proof point_defines_radius x x1 H3.
rewrite <- H0 in H6.

destruct H1.
pose proof point_defines_radius x0 x1 H4.
rewrite <- H1 in H8.

pose proof both_circles_same_radius (conj H0 H5) (conj H1 H7).
exact (eq_sym (radius_length_equal H9 H6 H8)).
Qed.

Definition Line := Ensemble Point.
Definition Ray := Ensemble Point.

Parameter make_ray : Point -> Point -> Ray.

Parameter make_line : Point -> Point -> Line.

Definition from_seg (a b : Point) : Line := make_line a b.
Definition from_seg_ray (a b : Point) : Ray := make_ray  a b.

Axiom make_seg : forall (a b : Point) (l : Line), l a /\ l b -> from_seg (a,b) = l.

Axiom line_intersect :
  forall (l1 l2 : Line),
    let intersection := Intersection Point l1 l2
    in (l1 = l2 -> intersection = l1) /\
       (l1 <> l2 -> ((exists (x : Point), intersection = Singleton Point x) \/
                     intersection = Empty_set Point)).

Definition seg_set := Ensemble Point.

Parameter make_seg_set : Point * Point -> seg_set.
Parameter from_seg_set : seg_set -> Point * Point.

Parameter from_seg_set_left_inv :
  forall (p1 p2 : Point), from_seg_set (make_seg_set (p1,p2)) = (p1,p2).

Parameter make_seg_set_right_inv :
  forall (l1 : seg_set), make_seg_set (from_seg_set l1) = l1.

Axiom seg_intersect :
  forall (l1 l2 : seg_set),
    let intersection := Intersection Point l1 l2
    in (l1 = l2 -> intersection = l1) /\
       (l1 <> l2 -> ((exists (x : Point), intersection = Singleton Point x) \/
                     intersection = Empty_set Point)).

Proposition prop_2 : forall (p a b : Point), exists (x : Point), length (a,b) = length (p,x).
Proof.
intuition.

(* If p = a *)
destruct (point_eq_or_not p a).
exists b.
rewrite e.
reflexivity.

(* Otherwise, follow euclid *)
destruct (prop_1 p a n).

destruct (circle a b).
pose proof make_line x b.

End Geometry.
