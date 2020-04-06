const faker = require('faker');
const jsonfile = require('jsonfile');

const numUsers = 10;
const udata = [];

faker.seed(1000);

for (let i = 1; i <= numUsers; i++) {
  const user = {
    id: "id-" + i,
    name: faker.internet.userName(),
  };
  udata.push(user);
}

const ufile = 'generated/Users.json';

jsonfile.writeFileSync(ufile, udata, function(err) {
  if (err) {
    console.error(err);
  } else {
    console.log('data created successfully');
  }
});
