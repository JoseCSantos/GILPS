%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-24
%
%    This file has predicates to generate a set of hypotheses with their respective
%  coverage, given a set of positive and negative examples and a predicate to generate
%  hypotheses from a positive example
%
%    The output of compute_coverage/4 is a list of hypotheses information. Each element
%    is a tuple of the form: (Hypothesis, HypothesisSignature, NumLiterals, ListExGen, ListExPos, ListExNeg)
%
%    where:
%      Hypothesis: is a unique hypothesis (with variables as a list of literals)
%      HypothesisSignature: Hypothesis signature
%      NumLiterals: number of literals in Hytpothesis
%      ListExGen: list of example ids that generated HypID
%      ListExPos: list of example ids of the positive examples covered
%      ListExNeg: list of example ids of the negative examples covered
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(hypotheses,
           [
             compute_hypotheses/5,
             compute_coverage/4
           ]
         ).

% GILPS modules
:- use_module('coverage', [hypothesis_coverage/6]).
:- use_module('score', [verifies_full_metrics/2, hypothesis_info/5]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [id2example/2, example/5]). %to access the examples
:- use_module('../messages/messages', [message/2]).

% YAP modules
:- use_module(library(rbtrees), [rb_new/1, rb_lookup/3, rb_insert/4, rb_update/4, rb_keys/2, rb_visit/2, rb_map/3, rb_size/2]).
:- use_module(library(lists), [reverse/2]).
:- use_module(library(apply_macros), [maplist/3]).
:- use_module(library(varnumbers), [varnumbers/2]). % this is an undocumented YAP library. varnumbers/2 does the inverse of numbervars/3

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% addExampleHypothesesAux(+Hypotheses, +ExampleID, +CurHypGenInfo, -NextHypGenInfo)
%
% Given:
%   Hypotheses: a list of hypothesis, each as a list of literals
%   ExampleID:  the exampleID that generated all the hypotheses
%   CurGenInfo: the current rb tree
%
% Returns:
%   NextHypGenInfo: updated rb tree by adding the head of each hypothesis in Hypotheses to it
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

addExampleHypothesesAux([], _ExampleID, HypGenInfo, HypGenInfo):-!.
addExampleHypothesesAux([(Hyp,HypSig)|Hyps], ExampleID, CurHypGenInfo, FinalHypGenInfo):-
  hypothesis2Key(Hyp, Key), % get the rb_tree key from hyp
  (rb_lookup(Key, (HypSig, NumLiterals, GenExamples), CurHypGenInfo) -> % check if Hyp was already in HypGenInfo
     (
      GenExamples=[ExampleID|_] -> % we do not want repetitions in list of examples that generated a given hypothesis
        NCurHypGenInfo = CurHypGenInfo
      ;
        rb_update(CurHypGenInfo, Key, (HypSig, NumLiterals, [ExampleID|GenExamples]), NCurHypGenInfo) % if it was, add example id to the list of generating examples
     )
    ;
    % should we keep both Key and Hyp in the hypothesis? we can convert between one and the other
     length(Hyp, NumLiterals),
     rb_insert(CurHypGenInfo, Key, (HypSig, NumLiterals, [ExampleID]), NCurHypGenInfo) % if it was not, create an entry and add example id as the unique element (so far)
  ),
  addExampleHypothesesAux(Hyps, ExampleID, NCurHypGenInfo, FinalHypGenInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% hypothesis2Key(+Hypothesis, -RBTreeKey)
%
% Given:
%   Hypothesis: an hypothesis as a list of literals
%
% Returns:
%   RBTreeKey: a unique key created from the hypothesis
%
% Notes:
%   The key to the rb_tree is Hypothesis reversed (to check efficiently for parents) and finally passed through
%   numbervars/3 to get rename the variables
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hypothesis2Key(Hypothesis, RBTreeKey):-
  copy_term(Hypothesis, TempHyp),     % copy Hypothesis to a new variable
  reverse(TempHyp, RBTreeKey),
  numbervars(RBTreeKey, 0, _). % the hypothesis Hyp after converted, after renaming through numbervars, is the key to the RB tree

%key2hypothesis(+RBTreeKey, -Hypothesis):-
key2hypothesis(RBTreeKey, Hypothesis):-
  varnumbers(RBTreeKey, TempHyp),
  reverse(TempHyp, Hypothesis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% addExampleHypotheses(+ExampleID, +APosEIDs, +ANegEIDs, +(CurExample, NumExamples), +HypGenPred, +CurHypGenInfo, -NextHypGenInfo)
%
%  Given:
%    ExampleID: The unique identifier of an example.
%    TPosEIDs: ordered list of positive example ids remaining (i.e. the subset from APosEIDs not yet considered)
%    APosEIDs: ordered list of all positive example ids (to possibly test for coverage)
%    ANegEIDs: ordered list of all negative example ids (to possibly test for coverage)
%    CurExample: Number of the current example (i.e. this is the CurExample-th processed example)
%    NumExamples: Total number of examples
%    HypGenPred: a predicate to generate hypotheses from examples
%    CurHypGenInfo: a red-black tree as described in compute_hypotheses/5
%
%  Returns:
%    NextHypGenInfo: has CurHypGenInfo updated with the hypotheses generated for the current example.
%                    Existing hypotheses, merely receive ExampleID as their generators
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate addExampleHypotheses(?, ?, ?, ?, ?, :, ?, ?). %the third argument, HypGenPred, is to be executed in its own module

addExampleHypotheses(ExampleID, TPosEIDs, APosEIDs, ANegEIDs, (CurExample, NumExamples), HypGenPred, CurHypGenInfo, NextHypGenInfo):-
  setting(nodes, MaxHypothesesPerExample),
  %example(ExampleID, Example, _Weight, _Fold, _RandomN), % retrieve the example, given the ExampleID
  %call_with_args(HypGenPred, Example, TPosEIDs, APosEIDs, ANegEIDs, MaxHypothesesPerExample, Hypotheses), % get the first MaxHypothesesPerExample Hypotheses that Example generates
  %example(ExampleID, Example, _Weight, _Fold, _RandomN), % retrieve the example, given the ExampleID
  call_with_args(HypGenPred, ExampleID, TPosEIDs, APosEIDs, ANegEIDs, MaxHypothesesPerExample, Hypotheses), % get the first MaxHypothesesPerExample Hypotheses that Example generates
  id2example(ExampleID, Example),

  message(hypotheses_for_example, [CurExample, NumExamples, Example, Hypotheses]),
  addExampleHypothesesAux(Hypotheses, ExampleID, CurHypGenInfo, NextHypGenInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_hypotheses(+PosEIDs, +APosEIDs, +ANegEIDs, +HypothesesGenPred, -HypGenInfo)
%
%  Given:
%   PosEIDs: list of positive examples from which we want to generate hypotheses from
%   APosEIDs: ordered list of positive example ids to possibly test coverage
%   ANegEIDs: ordered list of negative example ids to possibly test coverage
%   HypothesesGenPred: a predicate that takes generates Hypotheses from Examples
%                      (the first argument is an example id, the second is a list of hypotheses)
%
%  Returns:
%   HypGenInfo: a red black tree, with a grounded version (with numbervars/3) of the hypothesis (represented
%               by a reversed list of literals) as key and as value a tuple
%               (hypothesis signature, num literals, list of examples id that generated hypothesis)
%
%  Notes:
%    The hypothesis must pass through numbervars/3 before entering the rb_tree as key, otherwise two equal
%  hypothesis would be considered different. It is represented as a reversed list of literals to enable to
%  efficiently determine which hypotheses are parents of which.
%    The parent of an item with key [H|T] has key T. The examples a child hypothesis covers are a subset
%  of the ones the parent hypothesis covers.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate hypothesesAux(?, ?, ?, ?, :, ?, ?).

% hypothesesAux(+RemainPosEIDs, +APosEIDs, +ANegEIDs, +(CurExample, NumExamples), +HypGenPred, +CurHypGenInfo, -FinalHypGenInfo)
hypothesesAux([], _, _, _, _, HGI, HGI):-!.
hypothesesAux([PosEID|PosEIDs], APosEIDs, ANegEIDs, (CurExample, NumExamples), HypGenPred, CurHGI, FinalHGI):-
  CurExample1 is CurExample+1,
  addExampleHypotheses(PosEID, PosEIDs, APosEIDs, ANegEIDs, (CurExample1, NumExamples), HypGenPred, CurHGI, NHGI),
  hypothesesAux(PosEIDs, APosEIDs, ANegEIDs, (CurExample1, NumExamples), HypGenPred, NHGI, FinalHGI).

:- meta_predicate compute_hypotheses(?, ?, :, ?).

compute_hypotheses(PosEIDs, APosEIDs, ANegEIDs, HypGenPred, HypGenInfo):-
  rb_new(CurHypGenInfo),
  length(PosEIDs, NumExamples),
  hypothesesAux(PosEIDs, APosEIDs, ANegEIDs, (0, NumExamples), HypGenPred, CurHypGenInfo, HypGenInfo),
  rb_size(HypGenInfo, NumUniqueHypothesis),
  message(hypotheses_computed, [PosEIDs, NumUniqueHypothesis]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_coverage(+HypGenInfo, +PosExampleIDs, +NegExampleIDs, -HypothesesInfo)
%
%  Given:
%   HypGenInfo: a red black tree, with a grounded version (with numbervars/3) of the hypothesis (represented
%               by a reversed list of literals) as key and as value a tuple
%               (hypothesis signature,
%                hypothesis as a list of literals, num literals, list of examples id that generated hypothesis)
%   PosExampleIDs: list of ids of the positive examples to consider (used to generate hypgeninfo)
%   NegExampleIDs: list of ids of the negative examples to consider
%
%  Returns:
%   HypothesesInfo:  The output is a list of hypotheses information. Each element is a tuple of the form:
%                  (Hypothesis, HypSig, NumLiterals, ListExGen, ListExPos, ListExNeg)
%    where:
%      Hypothesis: is a unique hypothesis (with variables as a list of literals)
%      HypSignature: Hypothesis signature
%      NumLiterals: number of literals in Hytpothesis
%      ListExGen: list of example ids that generated HypID
%      ListExPos: list of example ids of the positive examples covered
%      ListExNeg: list of example ids of the negative examples covered
%
%  Notes:
%    HypTotInfo is a temporary variable that is a red black tree where each element is a tuple:
%              (HypSig, NumLiterals, ListExGen, ListExPos, ListExNeg)
%
%    where:
%      HypSig: hypothesis signature (i.e. signature for the rb tree key)
%      NumLiterals: number of literals in Hytpothesis
%      ExIDsGen: list of example ids that generated HypID
%      PosIDsCov: list of example ids of the positive examples covered
%      NegIDsCov: list of example ids of the negative examples covered
%    the key is hypothesis, with numbervars/3, as a reversed list of literals
%
%  Notes:
%    There are two implementations with and without smart_coverage, Smart_coverage only applies to TopLog
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_coverage(HypGenInfo, PosExampleIDs, NegExampleIDs, Hypotheses):-
  rb_new(InitialHypTotInfo),
  rb_visit(HypGenInfo, HypGenInfoList),
  rb_size(HypGenInfo, NumHypotheses),
  setting(smart_coverage, SC),
  setting(engine, Engine),
  (Engine=toplog, SC=true -> % only do smart coverage if it's on and for the TopLog engine
    maplist(processHypothesisList, HypGenInfoList, HypGenInfoList1),
    keysort(HypGenInfoList1, SHypGenInfoList), % we want to sort by ascending number of literals in order to process the parents before the children
    compute_coverage_smart(SHypGenInfoList, (0, NumHypotheses), HypGenInfo,
                           PosExampleIDs, NegExampleIDs, InitialHypTotInfo, HypTotInfo)
   ;
    compute_coverage_normal(HypGenInfoList, (0, NumHypotheses),
                           PosExampleIDs, NegExampleIDs, InitialHypTotInfo, HypTotInfo)
  ),
  message(total_coverage_computed, [NumHypotheses]),
  rb_visit(HypTotInfo, List_HypTotInfo),
  maplist(convertKey2Hyp, List_HypTotInfo, Hypotheses).

%convertKey2Hyp(+(Key-(HSig, NumLits, ExIDsGen, PosIDsCov, NegIDsCov)), -(Hypothesis, HSig, NumLits, ExIDsGen, PosIDsCov, NegIDsCov))
convertKey2Hyp(Key-(HSig, NumLits, ExIDsGen, PosIDsCov, NegIDsCov), (Hypothesis, HSig, NumLits, ExIDsGen, PosIDsCov, NegIDsCov)):-
  key2hypothesis(Key, Hypothesis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_coverage_normal(+HypGenInfoList, +(CurHypNumber, NumHyps), +PosExampleIDs, +NegExampleIDs, +CurHypTotInfo, -FinalHypTotInfo)
%
%    Implement compute_coverage/4 using always all examples (PosExampleIDs, NegExampleIDs), to compute the
%  coverage of a given hypothesis
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_coverage_normal([], _, _, _, HypTotInfo, HypTotInfo):-!.
compute_coverage_normal([(Key-(HSig, NumLiterals, GenExIDs))|Elems], (CurHypNumber, NumHyps),
                        PosExIDs, NegExIDs, CHTI, FHTI):-
  CurHypNumber1 is CurHypNumber+1,
  key2hypothesis(Key, Hypothesis),
  (good_hypothesis(Hypothesis, HSig, PosExIDs, NegExIDs, PosExIDs, NegExIDs, PosExIDsCov, NegExIDsCov) ->
     message(hypothesis_coverage_computed, [CurHypNumber1, NumHyps, Hypothesis, PosExIDsCov, NegExIDsCov]),
     rb_insert(CHTI, Key, (HSig, NumLiterals, GenExIDs, PosExIDsCov, NegExIDsCov), NCHTI),% add hypothesis to current hypothesis tree info
     compute_coverage_normal(Elems, (CurHypNumber1, NumHyps), PosExIDs, NegExIDs, NCHTI, FHTI)
   ;
     message(hypothesis_discarded, [CurHypNumber1, NumHyps, Hypothesis]),
     compute_coverage_normal(Elems, (CurHypNumber1, NumHyps), PosExIDs, NegExIDs, CHTI, FHTI) % ignore hypothesis
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% good_hypothesis(+Hypothesis, +HypSig, +TestHypPosEIDs, +TestHypNegEIDs, +AllPosEIDs, +AllNegEIDs, -PosEIDsCov, -NegEIDsCov)
%
% Given:
%  Hypothesis: an hypothesis as a list of literals
%  HypothesisSignature: hypothesis signature
%  TestHypPosEIDs: ordered list of positive examples to test for coverage
%  TestHypNegEIDs: ordered list of negatie examples to test for coverage
%  AllPosEIDs: ordered list of all positive examples to consider
%  AllNegEIDs: ordered list of all negative examples to consider
%
% Returns:
%  PosEIDsCov: ordered list of all positive examples covered (from TestHypPosEIDs)
%  NegEIDsCov: ordered list of all negative examples covered (from TestHypNegEIDs)
%
% Notes:
%  The reason for TestHyp and All is because of smart coverage. If smart coverage is false we could use always
%  All_. We don't just use TestHyp_ because it may be misleading for verifies_metrics for some metrics.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

good_hypothesis(Hypothesis, HypSig, TestHypPosEIDs, TestHypNegEIds, AllPosEIDs, AllNegEIDs, PosEIDsCov, NegEIDsCov):-
  hypothesis_coverage(Hypothesis, HypSig, TestHypPosEIDs, TestHypNegEIds, PosEIDsCov, NegEIDsCov), % signature is not known...
  hypothesis_info(PosEIDsCov, NegEIDsCov, AllPosEIDs, AllNegEIDs, HypInfo),
  length(Hypothesis, NumLiterals),
  verifies_full_metrics(NumLiterals, HypInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processHypothesisList(+(Key-(KeySig, NumLiterals, ListExGen)), -(NumLiterals-(Key, KeySig, ListExGen)))
%
%  Just puts NumLiterals at the beginning of the term, in order for key_sort to work correctly
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processHypothesisList((Key-(KeySig, NumLiterals, ListExGen)), (NumLiterals-(Key, KeySig, ListExGen))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_coverage_smart(+HypGenInfoList, +HypGenInfo, +(CurHypNumber, NumHyps), +PosExampleIDs, +NegExampleIDs, +CurHypTotInfo, -HypTotInfo)
%
%    Implements compute_coverage/4 using an hypothesis parent coverage as the basis for computing its
%  own coverage. This is logically sound and returns the same results being usually faster although there is
%  a small overhead for computing an hypothesis parent.
%    When an hypothesis has no parent all examples have to be used as before
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_coverage_smart([], _, _, _, _, HypTotInfo, HypTotInfo):-!.
compute_coverage_smart([NumLiterals-(Key, HSig, GenExIDs)|Elems], (CurHypNumber, NumHyps), HGI, PosExIDs, NegExIDs, CHTI, FHTI):-
  CurHypNumber1 is CurHypNumber+1,
  parentCoverage(Key, CHTI, PosExIDs, NegExIDs, ParentPosExIDs, ParentNegExIDs),
  key2hypothesis(Key, Hypothesis),
  % there is a parent hypothesis, so we will need to test the examples the parent covers
  (good_hypothesis(Hypothesis, HSig, ParentPosExIDs, ParentNegExIDs, PosExIDs, NegExIDs, PosExIDsCov, NegExIDsCov) ->
     message(hypothesis_coverage_computed, [CurHypNumber1, NumHyps, Hypothesis, PosExIDsCov, NegExIDsCov]),
     rb_insert(CHTI, Key, (HSig, NumLiterals, GenExIDs, PosExIDsCov, NegExIDsCov), NCHTI),% add hypothesis to current hypothesis tree info
     compute_coverage_smart(Elems, (CurHypNumber1, NumHyps), HGI, PosExIDs, NegExIDs, NCHTI, FHTI)
   ;
     message(hypothesis_discarded, [CurHypNumber1, NumHyps, Hypothesis]),
     compute_coverage_smart(Elems, (CurHypNumber1, NumHyps), HGI, PosExIDs, NegExIDs, CHTI, FHTI) % ignore hypothesis
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% parentKey(+ChildKey, -ParentKey)
%
%  Given:
%    ChildKey: the rbtree key for an hypothesis (a reversed list of ground literals)
%
%  Returns:
%    ParentKey: the rbtree key for the parent hypothesis
%
%  Notes:
%    We just need to delete the first literal as the list is already reversed
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

parentKey([_|T], T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% parentCoverage(+ChildKey, +CurHypTotInfo, +AllPosExampleIDs, +AllNegExampleIDs, -ParentPosExampleIDs, -ParentNegExampleIDs)
%
%  Given:
%    ChildKey: The key (a list of ground literals with numbervars/3) for the child hypothesis
%    Other input arguments: see above
%  Returns:
%    ParentPosExampleIDs: the coverage of the childkey hypothesis or AllPosExampleIDs if no parent exists
%    ParentNegExampleIDs: the coverage of the childkey hypothesis or AllNegExampleIDs if no parent exists
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

parentCoverage(Key, CHI, _AllPosExIDs, _AllNegExIDs, ParentPosExIDs, ParentNegExIDs):-
  parentKey(Key, PKey), % PKey is the key to the parent
  rb_lookup(PKey, (_KeySig, _NumLiterals, _ParentGenExIDs, ParentPosExIDs, ParentNegExIDs), CHI),
  !. % parent coverage exists, return it

parentCoverage(_Key, _CHI, AllPosExIDs, AllNegExIDs, AllPosExIDs, AllNegExIDs).
  % no parent exists, return all examples as coverage
