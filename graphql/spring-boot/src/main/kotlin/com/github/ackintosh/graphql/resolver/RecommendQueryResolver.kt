package com.github.ackintosh.graphql.resolver

import com.coxautodev.graphql.tools.GraphQLQueryResolver
import com.github.ackintosh.graphql.repository.RecommendRepository
import org.springframework.stereotype.Component

@Component
class RecommendQueryResolver(
        val recommendRepository: RecommendRepository
): GraphQLQueryResolver {

    fun getRecommend(id: Int) = recommendRepository.find(id)

    fun getRecommends() = recommendRepository.all()
}