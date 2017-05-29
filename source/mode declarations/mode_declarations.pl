%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-27
%
%  This file contains GILPS mode declarations
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(mode_declarations,
            [
              mode_head/1,
              modebDecls/1,

              eraseModeDeclarations/0,
              initModeDeclarations/0,
              update_default_recall/2,
              literal_recall/2,
              %checkForRecursiveModeDeclarations/0,
              recursive_mode_declarations/1,

              determinate_transformation/2,

             %these predicates are visible to the end user of GILPS, they are not to be used internally
              modeh/1,
              modeh/2,
              modeb/2,
              modeb/3
            ]
         ).

% GILPS modules
:- use_module('../utils/clause', [signatureConstIndexs/2, signature2PredArity/2]).
:- use_module('../settings/settings', [setting/2, set/2]). % because of setting(star_default_recall, R)
:- use_module('../utils/list', [merge_keys/2]).

% YAP modules
:- use_module(library(apply_macros), [maplist/3]).
:- use_module(library(lists), [max_list/2, member/2]).

:- dynamic(mode_head/1).
:- dynamic(recursive_mode_declarations/1).

% these are not needed as they are not externally accessible
%:- dynamic(mode_body/3).
%:- dynamic(predArity_recall/0).
:- dynamic(modebs_cache/1).
:- dynamic(cache_predicate_recall/2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  modeh(+Recall, +TargetSignature)
%
%     Add target as mode_head declaration. Recall is to be ignored, kept here just for compatibility
%  purposes with Aleph and Progol
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

modeh(Target):-
  modeh(_, Target).
modeh(_Recall, Target):-
  Target=not(_),!,
  format("GILPS warning:~N", []),
  format(" A mode head declaration cannot be negated.~N Offending modeh: ~w~N", [Target]),
  format(" This modeh declarating was ignored.~N", []),
  fail.
modeh(_Recall, Target):-
  retract(mode_head(OldTarget)),!,
  format("GILPS warning:~N", []),
  format("  A previous mode head definition already existed: ~w~N", [OldTarget]),
  format("  It has been retracted and replaced by ~w~N", [Target]),
  asserta(mode_head(Target)).
modeh(_Recall, Target):-
  asserta(mode_head(Target)). % silently add the target predicate for the first time

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  eraseModeDeclarations/0
%
%  Removes all mode head and mode body definitions.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eraseModeDeclarations:-
  retractall(mode_head(_)),
  retractall(mode_body(_, _)),
  retractall(modebs_cache(_)),
  retractall(predArity_recall(_)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  validModeBodySignature(+Signature)
%
%  Succeeds if Signature is a valid mode body signature. If not issues a warning and fails
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

validModeBodySignature(Signature):-
  Signature=not(not(_)),!,
  format("GILPS warning:~N", []),
  format("  A mode body declaration cannot have more than one not.~N  Offending modeb: ~w~N", [Signature]),
  format("  This modeb was ignored.~N", []),
  fail.
validModeBodySignature(not(Signature)):- % if we have a not, certify we have no constant indexs
  signatureConstIndexs(Signature, []), !.
validModeBodySignature(not(Signature)):- % if we have a not, certify we have no constant indexs
  !,
  format("GILPS warning:~N", []),
  format("  A negated mode body cannot have constants.~N  Offending modeb: not(~w)~N", [Signature]),
  format("  This modeb was ignored.~N", []),
  fail.
validModeBodySignature(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  validPredInfo(+PredInfo)
%
%  Succeeds if PredInfo is valid, otherwise outputs warning and fails
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

validPredInfo(normal):-!.
validPredInfo(commutative):-!.
validPredInfo(PredInfo):-
  format("GILPS warning:~N", []),
  format("  ~w is not a valid modeb qualifier. Valid qualifiers are: 'normal' and 'commutative'~N", [PredInfo]),
  format("  This modeb was ignored.~N", []),
  fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  modeb(+Recall, +PredicateSignature)
%  modeb(+Recall, +PredicateSignature, +PredInfo)
%
%  Given:
%    Recall: '*' or a positive integer
%    PredicateSignature: a predicate signature (e.g. atom(+drug,-atomid))
%    PredInfo: optional parameter. Either: 'normal' or 'commutative'
%
%  Succeeds by adding PredicateSignature as mode_body declaration with PredInfo associated
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

modeb(Recall, PredSignature):-
  modeb(Recall, PredSignature, normal). % if PredInfo omitted assume 'normal'
modeb(*, PredSignature, PredInfo):-
  !,
  setting(star_default_recall, Recall),
  modeb(Recall, PredSignature, PredInfo).
modeb(Recall, PredSignature, PredInfo):-
  validModeBodySignature(PredSignature),
  validPredInfo(PredInfo),!,
  assertz(mode_body(Recall, PredSignature, PredInfo)). % assertz so input order is maintained

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  modebDecls(-ModeBDecls)
%
%  Returns:
%    ModeBDecls: a list of the mode body declarations
%
%  E.g.
%    modebDecls([modeb(1, atom(+drug,-atomid)), modeb(1, bond(+drug,+atomid,-atomid))])
%
%  Notes:
%    ModeBDecls has modebs in the same order as they appear in the input file
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

modebDecls(ModeBDecls):-
  modebs_cache(ModeBDecls).
  %findall(modeb(RecallB, Signature, PredInfo), mode_body(RecallB, Signature, PredInfo), ModeBDecls).

%countClauses(+Signature, -NumClauses)
countClauses(Signature, NumClauses):-
  signature2PredArity(Signature, Name/Arity),
  functor(Func, Name, Arity),
  %predicate_property(user:Func, number_of_clauses(NumClauses)).
  (predicate_property(user:Func, number_of_clauses(NumClauses))-> true ; NumClauses=0). % in case of a recursive theory
  % there may be no definition for the recursive modeb predicate. This handles it

% cacheModebDecls/0
cacheModebDecls:-
  findall(NumClauses-modeb(RecallB, Signature, PredInfo),
          (mode_body(RecallB, Signature, PredInfo),
           countClauses(Signature, NumClauses)
          ),
          ModeBDecls),
  (setting(sort_mode_declarations, true) ->
    keysort(ModeBDecls, ModeBDecls1),
    maplist(removeKey, ModeBDecls1, ModeBDecls2)
   ;
    maplist(removeKey, ModeBDecls, ModeBDecls2)
  ),
  retractall(modebs_cache(_)),% JCAS: 09 September 2010: this retractall here is important, otherwise multiple solutions could be returned for modebs_cache, ultimately causing havoc in the theta subsumption clause evaluation engine! 
  asserta(modebs_cache(ModeBDecls2)).

removeKey(_Key-Value, Value).

% cachePredNameArityRecalls/0
cachePredNameArityRecalls:-
  findall(PredArity-Recall,
          (mode_body(Recall, Signature, _),
           signature2PredArity(Signature, PredArity)
          ),
          PredArities),
  % we could have done a findall followed by a keysort/2 rather than a all/3
  merge_keys(PredArities, PredArities1),
  maplist(maxlist, PredArities1, PredArities2),
  asserta(predArity_recall(PredArities2)).

maxlist(Key-Value, Key-Max):-
  max_list(Value, Max).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% checkForRecursiveModeDeclarations/0
%
% This predicate always succeeds and outputs its result as asserting either:
%   recursive_mode_declarations(true) or
%   recursive_mode_declarations(false)
%
% The modes are considered to be recursive if there is one modeb declaration with the same name
% and arity has the modeh declaration
%
% Notes:
%   This predicate must be called after the user file has been loaded (because otherwise we don't
%   know when we have seen all the mode declarations
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

checkForRecursiveModeDeclarations:-
  retractall(recursive_mode_declarations(_)), % in case it's not the first time we are calling checkRecursion
  mode_head(TargetSignature),
  signature2PredArity(TargetSignature, Name/Arity),
  findall(Signature, mode_body(_, Signature, _), ModeBSignatures),
  checkRecursionAux(ModeBSignatures, Name/Arity).

%checkRecursionAux(+ModeBSignatures, +(Name/Arity))

checkRecursionAux([], _):-
  asserta(recursive_mode_declarations(false)).
checkRecursionAux([Sig|_], Name/Arity):-
  signature2PredArity(Sig, Name/Arity),!,
  asserta(recursive_mode_declarations(true)),%assert
  dynamic(user:Name/Arity). % review: will give permission error if there is at least one static definition in user file
checkRecursionAux([_|Sigs], Name/Arity):-
  checkRecursionAux(Sigs, Name/Arity).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% determinate_transformation(+Clause, -TClause)
% determinate_transformation(+Clause, +Recalls, -TClause)
%
% Given:
%  Clause: a clause as a list of literals
%  Recalls: recalls of all the literals in Clause's body (does not include recall for the head)
%
% Returns:
%  TClause: transformed clause with determinate literals in the body of Clause encapsulated inside
%           a once/1 call
%
% Notes:
%  In order to determine if a literal is determinate we need its modeb declaration to look at the
%  recall. With just the literal we can compute its PredName/Arity but there is no guarantee of
%  a one to one relationship between PredName/Arity and modeb. The same PredName/Arity may have
%  several modebs (although this is unlikely). In such cases we just assume it's determinate
%  if the recall is '1' for all the compatible signatures
%
%  The cost of this transformation is O(N* number of unique mode body predname/arity)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determinate_transformation([Head|Body], [Head|NBody]):-
  literals_recalls(Body, Recalls),
  determinate_transformation_aux(Body, Recalls, NBody).

determinate_transformation([Head|Body], Recalls, [Head|NBody]):-
  determinate_transformation_aux(Body, Recalls, NBody).

determinate_transformation_aux([], [], []).
determinate_transformation_aux([Lit|Lits], [1|Recalls], [once(Lit)|NLits]):-
  !,
  determinate_transformation_aux(Lits, Recalls, NLits).
determinate_transformation_aux([Lit|Lits], [_|Recalls], [Lit|NLits]):-
  determinate_transformation_aux(Lits, Recalls, NLits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% literal_recall(+Literal, -Recall)
%
% Given:
%  Literal: a literal
%
% Returns:
%  Maximum recall for it from the mode declarations
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

literal_recall(Lit, Recall):-
  functor(Lit, Name, Arity),
  cache_predicate_recall(Name/Arity, Recall),!. % get it from cache
literal_recall(Lit, Recall):-
  functor(Lit, Name, Arity),
  predArity_recall(PredArityRecall),
  member((Name/Arity-Recall), PredArityRecall),!,
  asserta(cache_predicate_recall(Name/Arity, Recall)). % put it to cache

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% literals_recalls(+Literals, -Recalls)
%
% Given:
%  Literals: a list of literals (is not a clause, head is not included)
%
% Returns:
%  Recalls: a list of integers, the recalls of Literals
%
% Notes:
%  Since the PredName/Arity of a literal may lead to several recalls, the recall outputted is the
%  maximum recall of the possibilities
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

literals_recalls([], []).
literals_recalls([Lit|Lits], [Recall|Recalls]):-
  functor(Lit, Name, Arity),
  predArity_recall(PredArityRecall),
  member((Name/Arity-Recall), PredArityRecall),!,
  literals_recalls(Lits, Recalls).
literals_recalls([Lit|Lits], [2|Recalls]):- % give a 2 to not consider Lit determinate
  format("Warning: Unknown signature for ~w.~nClause incompatible with mode declarations?~n", [Lit]),
  format("This should never happen. Proceed at your own risk.~n", []),
  literals_recalls(Lits, Recalls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% update_default_recall(+OldRecall, +NewRecall)
%
% Resets the data structures so that default recall can be changed
%
% Note: Since we do not keep which of the predicates originally had a '*' we assume its all
% modeb declarations which have recall equal to the previous star_default_recall. Howver, there
% may be some modebs which were set to have recall to an integer which coincidentally is the
% previous default recall that will now be updated to the new recall.
%
% This in practice should not be a big issue. Nevertheless, in the future, fix this.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_default_recall(OldRecall, NewRecall):-
  retract(mode_body(OldRecall, PredSignature, PredInfo)),
  % although we are retracting and asserting the same predicate, we don't get to an infinite loop.
  assertz(mode_body(NewRecall, PredSignature, PredInfo)), % assertz so input order is maintained
  fail.
update_default_recall(_, _):-
  retractall(modebs_cache(_)),
  retractall(predArity_recall(_)),
  cacheModebDecls,
  cachePredNameArityRecalls.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initModeDeclarations/0
%
% Initializes global structures in this module
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initModeDeclarations:-
  cacheModebDecls,
  cachePredNameArityRecalls,
  checkForRecursiveModeDeclarations.
