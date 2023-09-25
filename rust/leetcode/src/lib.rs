extern crate core;

mod all_elements_in_two_binary_search_trees;
mod all_paths_from_source_to_target;
mod all_possible_full_binary_trees;
mod arithmetic_subarrays;
mod balance_a_binary_search_tree;
mod battleships_in_a_board;
mod binary_search_tree_to_greater_sum_tree;
mod build_an_array_with_stack_operations;
mod check_if_two_string_arrays_are_equivalent;
mod construct_binary_search_tree_from_preorder_traversal;
mod construct_smallest_number_from_di_string;
mod count_good_nodes_in_binary_tree;
mod count_items_matching_a_rule;
mod count_nodes_equal_to_average_of_subtree;
mod count_number_of_distinct_integers_after_reverse_operations;
mod count_number_of_maximum_bitwise_or_subsets;
mod count_odd_numbers_in_an_interval_range;
mod count_sorted_vowel_strings;
mod count_square_submatrices_with_all_ones;
mod count_the_number_of_consistent_strings;
mod count_triplets_that_can_form_two_arrays_of_equal_xor;
mod create_target_array_in_the_given_order;
mod decode_xored_array;
mod decompress_run_length_encoded_list;
mod deepest_leaves_sum;
mod defanging_an_ip_address;
mod delete_leaves_with_a_given_value;
mod design_a_stack_with_increment_operation;
mod design_browser_history;
mod design_parking_system;
mod design_underground_system;
mod difference_between_ones_and_zeros_in_row_and_column;
mod dp;
mod encode_and_decode_tinyurl;
mod equal_row_and_column_pairs;
mod execution_of_all_suffix_instructions_staying_in_a_grid;
mod find_all_duplicates_in_an_array;
mod find_and_replace_pattern;
mod find_center_of_star_graph;
mod find_elements_in_a_contaminated_binary_tree;
mod find_n_unique_integers_sum_up_to_zero;
mod find_the_original_array_of_prefix_xor;
mod find_the_prefix_common_array_of_two_arrays;
mod find_the_winner_of_the_circular_game;
mod find_triangular_sum_of_an_array;
mod find_valid_matrix_given_row_and_column_sums;
mod finding_the_users_active_minutes;
mod generate_parentheses;
mod goal_parser_interpretation;
mod group_the_people_given_the_group_size_they_belong_to;
mod how_many_numbers_are_smaller_than_the_current_number;
mod insert_into_a_binary_search_tree;
mod iterator_for_combination;
mod jewels_and_stones;
mod kids_with_the_greatest_number_of_candies;
mod largest_combination_with_bitwise_and_greater_than_zero;
mod letter_case_permutation;
mod letter_tile_possibilities;
mod lexicographically_smallest_equivalent_string;
mod march_leetcoding_challenge_2021;
mod matrix_block_sum;
mod max_increase_to_keep_city_skyline;
mod maximum_69_number;
mod maximum_binary_tree;
mod maximum_difference_between_node_and_ancestor;
mod maximum_ice_cream_bars;
mod maximum_number_of_coins_you_can_get;
mod maximum_number_of_words_found_in_sentences;
mod maximum_product_difference_between_two_pairs;
mod maximum_product_of_two_elements_in_an_array;
mod maximum_sum_of_an_hourglass;
mod maximum_twin_sum_of_a_linked_list;
mod maximum_xor_after_operations;
mod maximum_xor_for_each_query;
mod merge_in_between_linked_lists;
mod merge_nodes_in_between_zeros;
mod minimize_maximum_pair_sum_in_array;
mod minimum_add_to_make_parentheses_valid;
mod minimum_amount_of_time_to_collect_garbage;
mod minimum_number_of_operations_to_move_all_balls_to_each_box;
mod minimum_number_of_steps_to_make_two_strings_anagram;
mod minimum_number_of_vertices_to_reach_all_nodes;
mod minimum_operations_to_make_array_equal;
mod minimum_suffix_flips;
mod minimum_time_visiting_all_points;
mod number_of_good_pairs;
mod number_of_laser_beams_in_a_bank;
mod number_of_pairs_of_strings_with_concatenation_equal_to_target;
mod number_of_steps_to_reduce_a_number_to_zero;
mod optimal_partition_of_string;
mod palindrome_number;
mod partition_array_according_to_given_pivot;
mod partition_array_such_that_maximum_difference_is_k;
mod partition_labels;
mod partitioning_into_minimum_number_of_deci_binary_numbers;
mod path_in_zigzag_labelled_binary_tree;
mod permutations;
mod queries_on_a_permutation_with_key;
mod queries_on_number_of_points_inside_a_circle;
mod queue_reconstruction_by_height;
mod rearrange_array_elements_by_sign;
mod remove_all_occurrences_of_a_substring;
mod remove_outermost_parentheses;
mod removing_stars_from_a_string;
mod reveal_cards_in_increasing_order;
mod reverse_odd_levels_of_binary_tree;
mod richest_customer_wealth;
mod rotate_image;
mod running_sum_of_1d_array;
mod score_after_flipping_matrix;
mod shuffle_string;
mod shuffle_the_array;
mod smallest_number_in_infinite_set;
mod sort_the_matrix_diagonally;
mod sort_the_students_by_their_kth_score;
mod sort_vowels_in_a_string;
mod spiral_matrix_iv;
mod split_a_string_in_balanced_strings;
mod subdomain_visit_count;
mod subrectangle_queries;
mod subsets;
mod subtract_the_product_and_sum_of_digits_of_an_integer;
mod sum_of_nodes_with_even_valued_grandparent;
mod the_k_th_lexicographical_string_of_all_happy_strings_of_length_n;
mod truncate_sentence;
mod unique_number_of_occurrences;
mod water_bottles;
mod watering_plants;
mod xor_operation_in_an_array;

// mod test {
//     use std::cell::RefCell;
//     use std::rc::Rc;
//     use super::*;
//
//     #[allow(clippy::unnecessary_wraps)]
//     fn new_tree_node(
//         val: i32,
//         left: Option<Rc<RefCell<TreeNode>>>,
//         right: Option<Rc<RefCell<TreeNode>>>,
//     ) -> Option<Rc<RefCell<TreeNode>>> {
//         Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
//     }
//
//     #[test]
//     fn test() {
//         let root = new_tree_node(
//             1,
//             new_tree_node(
//                 2,
//                 new_tree_node(2, None, None),
//                 None,
//             ),
//             new_tree_node(
//                 3,
//                 new_tree_node(2, None, None),
//                 new_tree_node(4, None, None),
//             )
//         );
//         let answer = Solution::remove_leaf_nodes(root, 2);
//         println!("{:?}", answer);
//     }
// }
