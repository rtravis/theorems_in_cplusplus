/*
 * theorem_util.hpp
 *
 *  Created on: Feb 1, 2020
 *      Author: Robert Zavalczki
 */

#include <type_traits>

template<typename T, template<typename...> typename Template>
struct is_specialization_of : std::false_type {};

template<template<typename...> typename Template, typename... Args>
struct is_specialization_of<Template<Args...>, Template> : std::true_type {};

template<typename T, template<typename...> typename Template>
inline constexpr bool is_specialization_of_v = is_specialization_of<T, Template>::value;
