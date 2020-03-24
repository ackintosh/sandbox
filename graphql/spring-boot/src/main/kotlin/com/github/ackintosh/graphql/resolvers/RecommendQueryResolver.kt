package com.github.ackintosh.graphql.resolvers

import com.coxautodev.graphql.tools.GraphQLQueryResolver
import com.github.ackintosh.graphql.types.Recommend
import org.springframework.stereotype.Component

@Component
class RecommendQueryResolver: GraphQLQueryResolver {
    private val recommends = mapOf(
            1 to Recommend(1, "テレワークにお役立ちのアイテム集合！"),
            2 to Recommend(2, "わけあり商品！")
    )

    fun getRecommend(id: Int) = recommends[id]

    fun getRecommends() = recommends.values
}