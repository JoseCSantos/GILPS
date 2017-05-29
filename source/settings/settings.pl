%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-21
%
%
%     This file contains GILPS configuration settings
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(settings,
            [
              set/2,
              setting/2,
              show_settings/0
            ]
         ).

% YAP modules
:- use_module('../mode declarations/mode_declarations', [update_default_recall/2]).

:- dynamic(setting/2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% defaultSettings/0
%
% Sets GILPS to its default settings
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

defaultSettings:-
  % 'bottom_early_stop' : either true of false. If true and there are output variables in the modeh, stops
  % the construction of the bottom clause in the earliest layer where all the output variables have occurred.
  % if false or there are no output variables, constructs the bottom clause normally up to depth 'i'
  asserta(setting(bottom_early_stop, false)),
  %
  % clause_evaluation: either 'left_to_right', 'smallest_predicate_domain', 'smallest_variable_domain'
  %   'left_to_right': uses Prolog normal left to right, depth first clause evaluation
  %   'smallest_predicate_domain': chooses at each moment the literal with fewest solutions
  %                                from the ones which can be called (i.e. have their input variables bound)
  %   'smallest_variable_domain': chooses at each moment the variable with fewest solutions.
  %   'advanced': improvement over 'smallest_variable_domain' dividing the graph in components
  %   'theta_subsumption': performs theta-subsumption between hypothesis and example (example needs to be given as a (ground) clause)
  %
  %    The last two heuristics are much more efficient (several orders of magnitude) than 'left_to_right'
  %    but may have a non negligible overhead for small clauses (i.e. less than 10 literals) with recall=1.
  %
  %    The choice between 'smallest_predicate_domain' and 'smallest_variable_domain' should be based on
  %    the expected number of distinct variables vs number of literals in a clause. In general there are
  %    far fewer distinct variables than literals, and thus 'smallest_variable_domain' should be used.
  %
  asserta(setting(clause_evaluation, smallest_predicate_domain)), % changed from left_to_right on 10th March 2010, after ILP10 paper showing it's the most balanced choice overall
  % upper bound on number of literals in an acceptable clause (including head).
  asserta(setting(clause_length, 4)),
  %
  % Number of folds for doing cross validation. A positive integer (>=1) number of folds for cross validation
  %  (1 means use all data as training)
  % This has to be defined before the read_problem/1 call, otherwise was no effect!
  asserta(setting(cross_validation_folds, 1)),
  %
  % cut_transformation: either 'true' or 'false'
  %    true: applies the cut transformation (see paper:
  %                                 Query Transformations for Improving the Efficiency of ILP systems)
  %          this transformation occurs once per clause and has a cost O(N^2) (N=#clause literals)
  %          but in generals speeds up the entailment tests significantly
  %    false: do not enable cut transformation
  %
  asserta(setting(cut_transformation, false)), % this should be true by default, but is not yet compatible with dynamic clause evaluation  
  % maximum proof depth per goal. Is the depth (in terms of stack calls) we are willing to go to prove a goal
  asserta(setting(depth, 20)),
  %
  % determinate_transformation: either 'true' or 'false'
  %    true: applies the determination transformation, which consists in putting a once in each
  %          literal that is determinate. The cost of this transformation is:
  %                O(N*number of unique mode body predname/arity),  (N=#clause literals)
  %
  %    false: do not enable determinate transformation
  %
  asserta(setting(determinate_transformation, false)),
  %
  % The ILP engine to be run under the hood. Possible settings are:
  %   'toplog': Hypotheses are derived from a Top Theory compiled from the mode declarations
  %   'funclog': specific case when there's a single output variable
  %   'progolem': hypotheses are derived in a bottom up approach with assymmetric relative general generalization
  %
  % To implement:
  %    'progol'
  %    'auto'     : this requires being able to characterize what's the best algorithm for a problem
  %
  asserta(setting(engine, progolem)),
  %
  % Defines the evaluation function:
  %   compression: Clause utility is Pos - Neg - Literals + 1, 
  %     where Pos, Neg are the number of positive and negative examples covered by the clause, 
  %     and Literals the number of literals in the clause. 
  %   coverage: Clause utility is Pos - Neg,
  %     where Pos, Neg are the number of positive and negative examples covered by the clause. 
  %   laplace: Clause utility is (Pos+1)/(Pos+Neg+2),
  %     where Pos, Neg are the positive and negative examples covered by the clause.
  %
  asserta(setting(evalfn, compression)),
  %
  % evaluate_negatives_first:
  %           'true': when computing the coverage of a clause, compute first the negatives
  %                   so that we know if noise or maxneg was violated. This is specially useful
  %                   if maxneg is set to a low value and noise to 0.
  %           'false': compute positive coverage first so that we can put a threshold on
  %                    the maximum negatives to cover (it's noise * that value)
  %
  asserta(setting(evaluate_negatives_first, true)),
  %
  % example inflation: this value is multiplied by the weight of each individual example. It's
  % useful when there are few examples but we still want to generate a theory with evalfn=coverage
  % Note that if we set this to a negative number we have in fact just swapped the negative and positive examples
  %
  %  example_inflation must be set before read_problem/1 (otherwise it has no effect). I can fix this later
  %
  asserta(setting(example_inflation, 1)),
  % 'i' parameter of Progol and Aleph, layers of new variables when constructing bottom clause
  % in Aleph 'i' is one unit higher (e.g. i=1 in GILPS and Progol corresponds to i=2 in Aleph)
  asserta(setting(i, 3)),
  % maximum singletons in a clause
  asserta(setting(maximum_singletons_in_clause, inf)), % it's a positive integer or inf (for infinite)
  % maxneg: maximum negative weights a clause may cover
  asserta(setting(maxneg, inf)),
  %
  % max_uncompressive_examples: when doing incremental theory construction
  %   this is the maximum number of uncompressive (or whatever metric in use) we allow before stopping
  %   the algorithm (only applicable when theory_construction=incremental)
  %
  asserta(setting(max_uncompressive_examples, 20)),
  %
  %   Maximum number of clauses per theory: 'inf' means keep adding clauses to theory while there is a gain
  % in the evaluation metric. Any positive integer limits the theory to 'max_clauses_per_theory' clauses.
  %
  asserta(setting(max_clauses_per_theory, inf)),
  % minacc: minimum acceptable accuracy for the clause (considering all the confusion matrix!!)
  asserta(setting(minacc, 0)),
  % mincov: minimum percentage of (new) positive examples a rule has to cover
  asserta(setting(mincov, 0)),
  % minimum singletons in a clause
  asserta(setting(minimum_singletons_in_clause, 0)),
  % minpos: minimum positive weight a clause has to cover
  asserta(setting(minpos, 2)),
  % minprec: minimum acceptable percentage of corrected predicted positive examples per clause
  asserta(setting(minprec, 0)),  % the real value is the maximum between posprior and minprec (not 0)
  % minimum number of resolutions to give to any goal
  % the actual number of resolutions allowed is the resolutions plus
  % clause_length_resolutions_factor*actual_clause_length
  %
  % if we reach this bound goal is considered to fail, use '+inf' and not 'inf' for no limit
  asserta(setting(min_resolutions, 10000)),
  % negative_example_inflation: this value is multiplied by the weight of each negative example
  % (after applying regular example_inflation)
  asserta(setting(negative_example_inflation, 1)),
  %
  % negative_reduction_effort: either 'normal' or 'exhaustive'
  %   normal: removes (most) unnecessary literals from a clause (may still leave some literals that are redundant)
  %   (e.g. consider clause e(B):-l(A,B),f(A,B),o(B)), with e(B):-f(A,B),o(B) being the target concept)
  %   exhaustive: repeats the normal procedure until there are no redundant literals
  %
  asserta(setting(negative_reduction_effort, normal)),
  %
  % negative_reduction_measure: either 'consistency' or 'compressive'
  %   consistency: while negative reducing, we cannot entail negative examples
  %   auto: use the same as evalfn
  %   wprecision, accuracy, precision, compression, etc..: try to maximize this metric while reducing
  %
  asserta(setting(negative_reduction_measure, precision)),
  % noise: maximum acceptable percentage of miscovered negative weights per clause
  asserta(setting(noise, 0.5)),
  % upper bound on the number of hypotheses returned per example
  asserta(setting(nodes, 5000)),
  %
  % output_theory_file: the filename where the induced theory for all the training data is output
  %                     any existing file with the same will be overwritten
  %
  asserta(setting(output_theory_file, 'theory.pl')),
  %
  % Perform validation:
  %   If yes, use the examples that were not initially sampled to separately evaluate
  %   the induced theory. It only makes sense to be set to true when the sample parameter
  %   is below 1.0 
  %
%  asserta(setting(perform_validation, no)),
  % positive_example_inflation: this value is multiplied by the weight of each positive example
  % (after applying regular example_inflation)
  asserta(setting(positive_example_inflation, 1)),
  % Print parameter of Aleph: number of literals displayed per line when showing a clause
  asserta(setting(print, 4)),
  %
  % 'progolem_beam_width': keep up to 'progolem_beam_width' highest scoring clauses at each iteration
  % when constructing a theory with progolem.
  % (progolem_beam_width should be a fraction of progolem_iteration_sample_size)
  %
  asserta(setting(progolem_beam_width, 3)),
  %
  % progolem_bypass_coverage_iters:
  %          >0 : when computing progolem armg/srmg  avoid computing the coverage of the
  %               armg/srmg for the first 'progolem_bypass_coverage_iters' iterations,
  %               instead consider that the armg/srmg covers precisely the positive examples
  %               used to construct it and assume the negative coverage is empty
  %          '0': compute the coverage as normal
  %
  asserta(setting(progolem_bypass_coverage_iters, 0)),
  %
  % 'progolem_initial_pairs_sample': 
  %      number of pairs of positive examples to randomly choose when constructing a theory with progolem.
  %      'k' should be at least 2* max_clauses_per_theory in order for a randomly choosen clause
  %
  asserta(setting(progolem_initial_pairs_sample, 20)),
  %
  % 'progolem_iteration_sample_size':
  %      number of positives examples to choose at random to extend an existing armg
  %
  asserta(setting(progolem_iteration_sample_size, 20)),
  %
  % progolem_mode: the working mode of proglem. Can be either:
  %   single: bottom clause of an example is used as seed in Progolem and hill climbing with beam search of width
  %           'n' is performed afterwards with 'k' randomly selected examples
  %   reduce: bottom clause is reduced and that's the hypothesis
  %   pairs: 'k' pairs of randomly selected positived examples are constructed and the 'n' best are used as seed.
  %          (this is more efficient but cannot be used in global mode and is what golem used to do)
  %          Note that the pairs mode is not available in the global version of Progolem (in that case pairs=single)
  %
  asserta(setting(progolem_mode, single)),
  %
  % progolem_negative_sample_per_iteration:
  %           number of negative examples to use for reducing the armg at each iteration. 0 means do no reduction
  %
  asserta(setting(progolem_negative_sample_per_iteration, 0)),
  %
  % progolem_refinement_operator: the refinement operator progol uses to construct clauses
  %                               It can either be:
  %     'armg': assymmetric relative minimal generalization (positive clause reduction)
  %     'srmg': symetric relative minimal generalization (lggs between literals)
  %
  asserta(setting(progolem_refinement_operator, armg)),
  %
  % ProGolem Stochastic Beam: If false does a normal (i.e. greedy) beam search
  %                                              If true does a stochastic beam search (of the same beam width)
  %
  asserta(setting(progolem_stochastic_beam, false)),
  %
  % ProGolem Tournament Size: an integer > 1.  This only matters if progolem_stochastic_beam=true
  %                        When Progolem is in Stochastic mode we still select beam_width clauses for the next
  %                        iteration but they are selected by:
  %                            for(I=1; i<=BEAM_SIZE; i++) do
  %                                 Select randomly 'progolem_tournament_size' clauses from all clauses at the current iteration
  %                                 The winner clause (i.e. with highest score) is selected as a seed for the next iteration
  %                            end for
  %                         Note: this is done with replacement
  %
  asserta(setting(progolem_tournament_size, 2)),
  %
  % Set ProGolem's random seed: (this should be set before any random call is made!).
  %           That means before a call to build_theory
  %
  asserta(setting(random_seed, 7)), srandom(7), % this srandom/1 call must be here to ensure it's properly initialized
  %
  % randomize_recall: if true instead of pick the first N solutions for a predicate, picks N choosen randomly.
  % This impacts, in particular, the bottom clause generation and TopLog generated solutions for a predicate
  %
  asserta(setting(randomize_recall, false)), % this srandom/1 call must be here to ensure it's properly initialized
  %
  % recall_bound_on_evaluation: 
  %              +inf : evaluate a clause normally (Prolog semantics)
  %              >0: only allow any given literal in a clause to succeed up to this value.its recall
  %                  For determinate predicates it makes no difference, but for non determinate
  %                  predicates, this will be faster but the semantics are different. It may say a clause
  %                  does not cover an example, where with the Prolog sematics it would.
  %
  asserta(setting(recall_bound_on_evaluation, +inf)),
  %
  % remove_negative: this parameter is only used when theory_construction='incremental'. If set to true,
  %                  besides removing the positive examples covered by a clause, the negative examples are
  %                  also removed. This has the advantage of making the model construction faster since fewer
  %                  examples need to be evaluated.
  %                  On the downside: the new negatives covered is always equal to the total negatives covered
  %                  (the "old" negatives covered were removed before) and may return different clauses after
  %                  the first (e.g. due to the noise setting). For instance a clause which covered
  %                  5 new positives and 6 "old" negatives (i.e. negatives covered by previous clauses) would not 
  %                  be eligible, but if negatives are removed, this clause would be seen as just covering
  %                  5 positives and no negative
  %
  asserta(setting(remove_negatives, false)),
  % Sample: determines the percentage of examples to be used.
  % By default it is 1.0 which is all examples. This setting must be >0.0 and <=1.0
  asserta(setting(sample, 1.0)),
  % smart_coverage: when computing the coverage of a clause, if its parent coverage is available
  % use it. For datasets with many examples, this will decrease significantly the time required to
  % compute the hypotheses coverage. This is logically sound. It is only interesting to disable in
  % order to test the time taken without it. (it also has a small overhead that should not be significant)
  asserta(setting(smart_coverage, true)),
  %
  % if set to true the mode body declarations are sorted in ascending order according to the number of clauses
  % they represent (this may make ILP engines run faster)
  %
  asserta(setting(sort_mode_declarations, true)),
  %
  % split variables: if true splits the input and output variables of the head, and the output variables
  %                  of the body literals. This increases enormously the search space and is not needed
  %                  in many classification problems. However in some functional problems (i.e. when
  %                  there are output variables in the head) it may be very important. Examples
  %                  of problems where it's important are: binary relationships, numerical problems (n-choose-m)
  %
  asserta(setting(splitvars, false)),
  %
  % srmg_heuristic: sets the heuristics to use when computing srmgs. Possible values are:
  %             'first_match': the first matching atom is selected
  %             'minimize_negative': the atom that minimizes the negative coverage of the srmg is
  %                                  selected at each stage (this is much more expensive but
  %                                  should lead to better srmgs).
  %
  asserta(setting(srmg_heuristic, first_match)),
  % Default recall when a star '*' is entered in a modeb definition, this must be defined before read_problem/1, otherwise has no effect!
  asserta(setting(star_default_recall, 10)),
  %
  % theory_construction: may be either 'global' or 'incremental'. If 'global' then all hypotheses from all the
  %     examples are generated and only at the end the theory is constructed.
  %      If 'incremental' then the most compressive hypothesis per 'example' is added to the theory and the
  %     examples it covers are removed.
  %       Notice that 'global' is (much) slower than 'incremental' but is example order independent and allows
  %     for efficient cross validation. On the other hand, it's easier to learn recursive theories with
  %     'incremental'.
  %
  asserta(setting(theory_construction, global)),
  %
  % Defines the verbosity level:
  %     0: only outputs major milestones: 
  %                                       1) Computed all hypotheses
  %                                       2) Computed all coverages
  %                                       3) Computed greedy
  %                                       4) Show theory and confusion matrix
  %
  %     2: show everything that may be useful for debugging:
  %         all of previous verbosity levels plus
  %             1) Which are the ids of which examples
  %             2) The hypothesis and their coverages
  %             3) 
  % for close none 1 for some info, 2 for extra info
  asserta(setting(verbose, 1)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% description(+SettingName, -Description)
%
% Given:
%   SettingName: a name of the setting (e.g. depth)
%
% Returns:
%   Description: a short description of the setting
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

description(depth,         'Upper bound on the proof depth to which theorem-proving proceeds (default=10,min=1).').
description(clause_length, 'Upper bound on number of literals in an acceptable clause, including the head (default=4, min=1).').
description(nodes,         'Upper bound on the number of hypotheses returned per example (default=1000).').
description(example_inflation, 'The weight of each example is multiplied by this constant (default=1).').
description(cross_validation_folds, 'Num folds for cross validation. Values: positive integer>=1 (default=1, i.e. no CV).').
description(verbose,           'Verbosity level: 0 for almost none, 1 for some information, 2 for extra information.').
description(sample,            'Sample: percentage of examples to use (default=1, all examples). Must be >=0 and <=1.').
description(perform_validation,'Uses the non sampled examples to separately evaluate the induced theory. Values: yes, no (default=no).').
description(evalfn,            'Evaluation function: compression (default), coverage or laplace (i.e. adjusted accuracy).').
description(minimum_singletons_in_clause,  'Minimum number of singletons in an acceptable clause (default=0).').
description(maximum_singletons_in_clause,  'Maximum number of singletons in an acceptable clause (default=inf).').
description(noise,  'Maximum acceptable percentage of misclassified negative examples per clause (default=1.0).').
description(minacc, 'Minimum acceptable percentage of of covered positive weights per clause (default=0).').
description(minpos, 'Minimum positive weight a clause has to cover (default=0).').
description(maxneg, 'Maximum absolute negative weight a clause may cover (default=inf).').
description(smart_coverage, 'Test coverage using clause''s parent coverage rather than all examples (default=true).').
description(star_default_recall, 'Default recall when using a * in a modeb definition (default=100).').

% set(+Setting, +Value): change the setting Setting to new value Value

set(Setting, Value):-
  ground(Setting),
  ground(Value),!,
  retract(setting(Setting, OldValue)),
  asserta(setting(Setting, Value)),
  (Setting==random_seed -> 
     srandom(Value)   ;
   Setting==star_default_recall ->  % reset the mode declarations
     update_default_recall(OldValue, Value) ;
   true
  ).   

% set(?Setting, ?Value): returns Setting, Value or both depending on what is instantiated
set(Setting, Value):-
  setting(Setting, Value).

show_settings:-
  format("GILPS settings~2n", []),
  format("Setting~55+Value~2n", []),
  setting(Setting, Value),
  %description(Setting, Desc),
  format("~w~40+~t~w~20+~n", [Setting, Value]),
  fail.
show_settings.

:- initialization(defaultSettings).

