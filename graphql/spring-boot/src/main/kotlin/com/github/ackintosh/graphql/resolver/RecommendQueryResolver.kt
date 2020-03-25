package com.github.ackintosh.graphql.resolver

import com.coxautodev.graphql.tools.GraphQLQueryResolver
import com.github.ackintosh.graphql.repository.RecommendRepository
import com.github.ackintosh.graphql.type.Recommend
import org.springframework.stereotype.Component

@Component
class RecommendQueryResolver(
        val recommendRepository: RecommendRepository
): GraphQLQueryResolver {

    fun recommend(id: Int): Recommend? {
        println("RecommendQueryResolver::recommend")
        return recommendRepository.find(id)
    }

    fun recommends(): List<Recommend> {
        println("RecommendQueryResolver::recommends")
        return recommendRepository.all()
    }
}