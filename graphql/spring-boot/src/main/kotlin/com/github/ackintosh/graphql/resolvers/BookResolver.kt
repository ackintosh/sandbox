package com.github.ackintosh.graphql.resolvers

import com.coxautodev.graphql.tools.GraphQLResolver
import com.github.ackintosh.graphql.types.Author
import com.github.ackintosh.graphql.types.Book
import org.springframework.stereotype.Component

@Component
class BookResolver: GraphQLResolver<Author> {
    fun books(author: Author) = listOf(
            Book(1, "Book1", "Author1"),
            Book(2, "Book2", "Author2"),
            Book(3, "Book3", "Author3")
    )
}