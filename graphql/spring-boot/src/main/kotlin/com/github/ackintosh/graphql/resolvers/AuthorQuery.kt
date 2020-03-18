package com.github.ackintosh.graphql.resolvers

import com.coxautodev.graphql.tools.GraphQLQueryResolver
import com.github.ackintosh.graphql.types.Author
import org.springframework.stereotype.Component

@Component
class AuthorQuery: GraphQLQueryResolver {
    // Query名とメソッド名を揃える
    fun getAuthorById(id: Int) = Author(id, "test author")
}