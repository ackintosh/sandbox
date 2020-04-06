const chai = require('chai');
const expect = chai.expect;
const url = `http://localhost:62222`;
const request = require('supertest')(url);

describe('GraphQL endpoint', () => {
  it('Should return User', (done) => {
    request.post('/graphql')
      .send({ query: '{ user(id: "id-3") { id name } }'})
      .set('content-type', 'application/json')
      // API$BG'>Z%-!<(B: $BI,?\$@$1$I!"%-!<$OE,Ev$GNI$$(B
      .set('x-api-key', 'test-api-key')
      .expect(200)
      .end((error, response) => {
        if (error) {
          return done(err)
        }

        expect(response.body.data.user).have.property('id')
        expect(response.body.data.user).have.property('name')
        done()
      })
  })
})
